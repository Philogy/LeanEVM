import Evm.Machine.ExecutionStateOps
import Evm.Machine.MachineStateOps
import Evm.Maps.AccountMap
import Evm.Semantics.Precompiles
import Evm.Semantics.Decode
import Evm.Semantics.Frame
import Evm.Semantics.Params

namespace Evm

/--
Enter a message call — the YP's `Θ` (eq. 119) up to the recursive code
execution: value transfer (eq. 124–126), execution-environment construction
(eq. 132–141), and precompile dispatch.

Returns `.inl frame` when EVM code must run (the driver descends into it) or
`.inr result` when the call completes without code execution (precompiles).
-/
def beginCall (params : CallParams) : Frame ⊕ CallResult :=
  let σ := params.accounts
  -- (124) (125) (126)
  let σ'₁ :=
    match σ.find? params.recipient with
      | none =>
        if params.value != (0 : UInt256) then
          σ.insert params.recipient { (default : Account) with balance := params.value }
        else
          σ
      | some acc =>
        σ.insert params.recipient { acc with balance := acc.balance + params.value }

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σ₁ :=
    match σ'₁.find? params.caller with
      | none => σ'₁
      | some acc =>
        σ'₁.insert params.caller { acc with balance := acc.balance - params.value }

  let I : ExecutionEnv :=
    {
      codeOwner := params.recipient        -- Equation (132)
      sender    := params.origin           -- Equation (133)
      gasPrice  := params.gasPrice.toNat   -- Equation (134)
      calldata  := params.calldata         -- Equation (135)
      source    := params.caller           -- Equation (136)
      weiValue  := params.apparentValue    -- Equation (137)
      depth     := params.depth            -- Equation (138)
      perm      := params.canModifyState   -- Equation (139)
      -- Note that we don't use an address, but the actual code. Equation (141)-ish.
      code      :=
        match params.codeSource with
          | ToExecute.Precompiled _ => default
          | ToExecute.Code code => code
      header    := params.blockHeader
      blobVersionedHashes := params.blobVersionedHashes
    }

  match params.codeSource with
    | ToExecute.Precompiled p =>
      let (z, σ'', g', A'', out) :=
        match p with
          | 1  => Precompiles.ecRecover        σ₁ params.gas params.substate I
          | 2  => Precompiles.sha256           σ₁ params.gas params.substate I
          | 3  => Precompiles.ripemd160        σ₁ params.gas params.substate I
          | 4  => Precompiles.identity         σ₁ params.gas params.substate I
          | 5  => Precompiles.modExp           σ₁ params.gas params.substate I
          | 6  => Precompiles.ecAdd            σ₁ params.gas params.substate I
          | 7  => Precompiles.ecMul            σ₁ params.gas params.substate I
          | 8  => Precompiles.ecPairing        σ₁ params.gas params.substate I
          | 9  => Precompiles.blake2f          σ₁ params.gas params.substate I
          | 10 => Precompiles.pointEvaluation  σ₁ params.gas params.substate I
          | _  => (false, ∅, 0, params.substate, .empty) -- unreachable: `toExecute` yields 1–10 only
      .inr
        -- NB the precompile path historically clears `createdAccounts`; kept verbatim.
        { createdAccounts := ∅
          -- Equations (127) and (129): an empty post-map signals failure — roll back.
          accounts := if σ'' == ∅ then σ else σ''
          gasRemaining := g'
          substate := if σ'' == ∅ then params.substate else A''
          success := z
          output := out }
    | ToExecute.Code _ =>
      .inl
        { kind := .call ⟨params.createdAccounts, σ, params.substate⟩
          validJumps := validJumpDests I.code 0
          exec :=
            { (default : ExecutionState) with
                accountMap := σ₁
                σ₀ := params.originalAccounts
                executionEnv := I
                substate := params.substate
                createdAccounts := params.createdAccounts
                gasAvailable := params.gas
                blocks := params.blocks
                genesisBlockHeader := params.genesisBlockHeader } }

/--
Finish a message call — the YP's `Θ` after code execution: package the halt
into the call's result, rolling back to the checkpoint on failure
(eq. 127, 129).
-/
def endCall (checkpoint : Checkpoint) : FrameHalt → CallResult
  | .success exec output =>
    let σ'' := exec.accountMap
    { createdAccounts := exec.createdAccounts
      -- Equations (127) and (129)
      accounts := if σ'' == ∅ then checkpoint.accounts else σ''
      gasRemaining := exec.gasAvailable
      substate := if σ'' == ∅ then checkpoint.substate else exec.substate
      success := true
      output := output }
  | .revert gasRemaining output =>
    { createdAccounts := checkpoint.createdAccounts
      accounts := checkpoint.accounts
      gasRemaining := gasRemaining
      substate := checkpoint.substate
      success := false
      output := output }
  | .exception _ =>
    { createdAccounts := checkpoint.createdAccounts
      accounts := checkpoint.accounts
      gasRemaining := 0
      substate := checkpoint.substate
      success := false
      output := .empty }

/--
Resume a frame suspended on a CALL-family instruction: write the call output
to memory, restore the returned gas, push the success flag, and advance the
pc. This is the post-`Θ` tail of the CALL instructions.
-/
def resumeAfterCall (result : CallResult) (pd : PendingCall) : Frame :=
  let evmState := pd.frame.exec
  let o := result.output
  -- n ≡ min({μs[6], ‖o‖})
  let n : UInt256 := min pd.outSize (.ofNat o.size)
  -- μ′_m[μs[5] ... (μs[5] + n − 1)] = o[0 ... (n − 1)]
  let μ'ₘ := writeBytes o 0 evmState.toMachineState pd.outOffset.toNat n.toNat
  let μ'_g := μ'ₘ.gasAvailable + result.gasRemaining -- Ccall was subtracted as part of C

  let codeExecutionFailed   : Bool := !result.success
  let notEnoughFunds        : Bool :=
    pd.value > (pd.callerAccounts.find? evmState.executionEnv.codeOwner |>.elim 0 (·.balance))
  let callDepthLimitReached : Bool := evmState.executionEnv.depth == 1024
  -- x = 0 if the code execution failed, there were not enough funds, or the
  -- call depth limit was reached; x = 1 otherwise.
  let x : UInt256 := if codeExecutionFailed || notEnoughFunds || callDepthLimitReached then 0 else 1

  let μ' : MachineState :=
    { μ'ₘ with
        returnData   := o -- μ′o = o
        gasAvailable := μ'_g
        activeWords :=
          let m : ℕ := MachineState.M evmState.toMachineState.activeWords.toNat pd.inOffset.toNat pd.inSize.toNat
          .ofNat <| MachineState.M m pd.outOffset.toNat pd.outSize.toNat }

  let exec' : ExecutionState :=
    { evmState with
        accountMap := result.accounts
        substate := result.substate
        createdAccounts := result.createdAccounts
        toMachineState := μ' }
  { pd.frame with exec := exec'.replaceStackAndIncrPC (pd.stack.push x) }

end Evm
