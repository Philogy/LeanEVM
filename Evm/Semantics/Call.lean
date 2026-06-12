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
  let accounts := params.accounts
  -- (124) (125) (126)
  let accountsAfterCredit :=
    match accounts.find? params.recipient with
      | none =>
        if params.value != (0 : UInt256) then
          accounts.insert params.recipient { (default : Account) with balance := params.value }
        else
          accounts
      | some acc =>
        accounts.insert params.recipient { acc with balance := acc.balance + params.value }

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let accountsAfterTransfer :=
    match accountsAfterCredit.find? params.caller with
      | none => accountsAfterCredit
      | some acc =>
        accountsAfterCredit.insert params.caller { acc with balance := acc.balance - params.value }

  let env : ExecutionEnv :=
    {
      address := params.recipient        -- Equation (132)
      origin    := params.origin           -- Equation (133)
      gasPrice  := params.gasPrice.toNat   -- Equation (134)
      calldata  := params.calldata         -- Equation (135)
      caller    := params.caller           -- Equation (136)
      value  := params.apparentValue    -- Equation (137)
      depth     := params.depth            -- Equation (138)
      canModifyState      := params.canModifyState   -- Equation (139)
      -- Note that we don't use an address, but the actual code. Equation (141)-ish.
      code      :=
        match params.codeSource with
          | ToExecute.Precompiled _ => default
          | ToExecute.Code code => code
      blockHeader := params.blockHeader
      blobVersionedHashes := params.blobVersionedHashes
      chainId   := params.chainId
    }

  match params.codeSource with
    | ToExecute.Precompiled p =>
      let (success, accounts'', gasRemaining, substate'', output) :=
        match p with
          | 1  => Precompiles.ecRecover        accountsAfterTransfer params.gas params.substate env
          | 2  => Precompiles.sha256           accountsAfterTransfer params.gas params.substate env
          | 3  => Precompiles.ripemd160        accountsAfterTransfer params.gas params.substate env
          | 4  => Precompiles.identity         accountsAfterTransfer params.gas params.substate env
          | 5  => Precompiles.modExp           accountsAfterTransfer params.gas params.substate env
          | 6  => Precompiles.ecAdd            accountsAfterTransfer params.gas params.substate env
          | 7  => Precompiles.ecMul            accountsAfterTransfer params.gas params.substate env
          | 8  => Precompiles.ecPairing        accountsAfterTransfer params.gas params.substate env
          | 9  => Precompiles.blake2f          accountsAfterTransfer params.gas params.substate env
          | 10 => Precompiles.pointEvaluation  accountsAfterTransfer params.gas params.substate env
          | _  => (false, ∅, 0, params.substate, .empty) -- unreachable: `toExecute` yields 1–10 only
      .inr
        -- NB the precompile path historically clears `createdAccounts`; kept verbatim.
        { createdAccounts := ∅
          -- Equations (127) and (129): an empty post-map signals failure — roll back.
          accounts := if accounts'' == ∅ then accounts else accounts''
          gasRemaining := gasRemaining
          substate := if accounts'' == ∅ then params.substate else substate''
          success := success
          output := output }
    | ToExecute.Code _ =>
      .inl
        { kind := .call ⟨params.createdAccounts, accounts, params.substate⟩
          validJumps := validJumpDests env.code 0
          exec :=
            { (default : ExecutionState) with
                accounts := accountsAfterTransfer
                originalAccounts := params.originalAccounts
                executionEnv := env
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
    let accounts'' := exec.accounts
    { createdAccounts := exec.createdAccounts
      -- Equations (127) and (129)
      accounts := if accounts'' == ∅ then checkpoint.accounts else accounts''
      gasRemaining := exec.gasAvailable
      substate := if accounts'' == ∅ then checkpoint.substate else exec.substate
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
  let output := result.output
  -- outputWriteLen ≡ min({μs[6], ‖output‖})
  let outputWriteLen : ℕ := min pd.outSize.toNat output.size
  -- μ′_m[μs[5] ... (μs[5] + outputWriteLen − 1)] = output[0 ... (outputWriteLen − 1)]
  let machineWithOutput := writeBytes output 0 evmState.toMachineState pd.outOffset.toNat outputWriteLen
  let gasAfterReturn := machineWithOutput.gasAvailable + result.gasRemaining -- Ccall was subtracted as part of C

  let codeExecutionFailed   : Bool := !result.success
  let notEnoughFunds        : Bool :=
    pd.value > (pd.callerAccounts.find? evmState.executionEnv.address |>.elim 0 (·.balance))
  let callDepthLimitReached : Bool := evmState.executionEnv.depth == 1024
  -- x = 0 if the code execution failed, there were not enough funds, or the
  -- call depth limit was reached; x = 1 otherwise.
  let x : UInt256 := if codeExecutionFailed || notEnoughFunds || callDepthLimitReached then 0 else 1

  let μ' : MachineState :=
    { machineWithOutput with
        returnData   := output -- μ′output = output
        gasAvailable := gasAfterReturn
        activeWords :=
          let m := MachineState.M evmState.toMachineState.activeWords pd.inOffset pd.inSize
          MachineState.M m pd.outOffset pd.outSize }

  let exec' : ExecutionState :=
    { evmState with
        accounts := result.accounts
        substate := result.substate
        createdAccounts := result.createdAccounts
        toMachineState := μ' }
  { pd.frame with exec := exec'.replaceStackAndIncrPC (pd.stack.push x) }

end Evm
