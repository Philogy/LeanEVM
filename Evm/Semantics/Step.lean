import Evm.Gas
import Evm.GasConstants
import Evm.Semantics.Call
import Evm.Semantics.Create
import Evm.Semantics.Decode
import Evm.Semantics.Frame
import Evm.Step

namespace Evm

/--
The state-modifying instructions `W` (eq. 159) — forbidden when the frame
lacks `perm` (static call context).
-/
private def W (w : Operation) (s : Stack UInt256) : Bool :=
  match w with
    | .CREATE | .CREATE2 | .SSTORE | .SELFDESTRUCT
    | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 | .TSTORE => true
    | .CALL => s[2]? ≠ some 0
    | _ => false

private def belongs (o : Option UInt256) (l : Array UInt256) : Bool :=
  match o with
    | none => false
    | some n => l.contains n

private def notIn (o : Option UInt256) (l : Array UInt256) : Bool := not (belongs o l)

/--
Exceptional-halt checks `Z` (eq. 158) plus the gas charge: validates the
instruction against the current state, charges the memory-expansion cost, and
returns the updated state together with the instruction's remaining gas cost
(charged by the instruction itself).
-/
private def Z (validJumps : Array UInt256) (w : Operation) (evmState : ExecutionState) :
    Except ExecutionException (ExecutionState × ℕ) := do
  -- The stack-depth check precedes the cost computations: both
  -- memoryExpansionCost and C' peek at stack slots with `!`.
  if δ w = none then
    .error .InvalidInstruction
  if evmState.stackSize < (δ w).getD 0 then
    .error .StackUnderflow
  let cost₁ := memoryExpansionCost evmState w
  if evmState.gasAvailable.toNat < cost₁ then
    .error .OutOfGass
  let gasAvailable := evmState.gasAvailable - .ofNat cost₁
  let evmState := { evmState with gasAvailable := gasAvailable }
  let cost₂ := C' evmState w

  if evmState.gasAvailable.toNat < cost₂ then
    .error .OutOfGass

  let invalidJump := notIn evmState.stack[0]? validJumps

  if w = .JUMP ∧ invalidJump then
    .error .BadJumpDestination

  if w = .JUMPI ∧ (evmState.stack[1]? ≠ some 0) ∧ invalidJump then
    .error .BadJumpDestination

  if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 0).toNat + (evmState.stack.getD 2 0).toNat > evmState.returnData.size then
    .error .InvalidMemoryAccess

  if evmState.stackSize - (δ w).getD 0 + (α w).getD 0 > 1024 then
    .error .StackOverflow

  if (¬ evmState.executionEnv.perm) ∧ W w evmState.stack then
    .error .StaticModeViolation

  if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
    .error .OutOfGass

  if
    w.isCreate ∧ evmState.stack.getD 2 0 > 49152
  then
    .error .OutOfGass

  pure (evmState, cost₂)

/-- The normal-halt discriminator `H` (eq. 146-ish). -/
private def H (μ : MachineState) (w : Operation) : Option ByteArray :=
  match w with
    | .RETURN | .REVERT => some μ.H_return
    | .STOP | .SELFDESTRUCT => some .empty
    | _ => none

/--
Shared tail of the CALL-family instructions: compute the child's gas
allowance, charge the instruction cost, read the input data, and either
suspend on the child call (`.needsCall`) or — when the balance/depth
pre-checks fail — complete the instruction immediately with a failed-call
result.
-/
private def prepareCall (fr : Frame) (evmState : ExecutionState) (gasCost : ℕ)
    (stack : Stack UInt256)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) : StepOutcome :=
  let t : AccountAddress := AccountAddress.ofUInt256 t
  let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
  let source : AccountAddress := AccountAddress.ofUInt256 source
  let Iₐ := evmState.executionEnv.codeOwner
  let σ := evmState.accountMap
  let Iₑ := evmState.executionEnv.depth
  let callgas := Ccallgas t recipient value gas σ evmState.toMachineState evmState.substate
  let evmState := { evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost }
  -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
  let i := evmState.memory.readWithPadding inOffset.toNat inSize.toNat
  let A' := evmState.addAccessedAccount t |>.substate
  let pending : PendingCall :=
    { frame := { fr with exec := evmState }
      stack := stack
      callerAccounts := σ
      value := value
      inOffset := inOffset
      inSize := inSize
      outOffset := outOffset
      outSize := outSize }
  if value ≤ (σ.find? Iₐ |>.option 0 (·.balance)) ∧ Iₑ < 1024 then
    .needsCall
      { blobVersionedHashes := evmState.executionEnv.blobVersionedHashes
        createdAccounts := evmState.createdAccounts
        genesisBlockHeader := evmState.genesisBlockHeader
        blocks := evmState.blocks
        accounts := σ                                       -- σ in  Θ(σ, ..)
        originalAccounts := evmState.σ₀
        substate := A'                                      -- A* in Θ(.., A*, ..)
        caller := source
        origin := evmState.executionEnv.sender              -- Iₒ in Θ(.., Iₒ, ..)
        recipient := recipient                              -- t in Θ(.., t, ..)
        codeSource := toExecute σ t
        gas := .ofNat callgas
        gasPrice := .ofNat evmState.executionEnv.gasPrice   -- Iₚ in Θ(.., Iₚ, ..)
        value := value
        apparentValue := value'
        calldata := i
        depth := Iₑ + 1
        blockHeader := evmState.executionEnv.header
        canModifyState := permission }                      -- I_w in Θ(.., I_W)
      pending
  else
    -- otherwise (σ, CCALLGAS(σ, μ, A), A, 0, ()) — the call never happens;
    -- the child's gas allowance returns to the caller untouched.
    let failed : CallResult :=
      { createdAccounts := evmState.createdAccounts
        accounts := σ
        gasRemaining := .ofNat callgas
        substate := A'
        success := false
        output := .empty }
    .next (resumeAfterCall failed pending).exec

/--
Shared tail of CREATE/CREATE2: charge the instruction cost, bump the
creator's nonce, and either suspend on the init-code execution
(`.needsCreate`) or — when the nonce/balance/depth/init-code-size pre-checks
fail — complete the instruction immediately with a failed-creation result.
-/
private def prepareCreate (fr : Frame) (evmState : ExecutionState)
    (stack : Stack UInt256) (value initOffset initSize : UInt256)
    (ζ : Option ByteArray) : Except ExecutionException StepOutcome := do
  let i := evmState.memory.readWithPadding initOffset.toNat initSize.toNat
  let I := evmState.executionEnv
  let Iₐ := I.codeOwner
  let Iₑ := I.depth
  let σ := evmState.accountMap
  let σ_Iₐ : Account := σ.find? Iₐ |>.getD default
  let σStar := σ.insert Iₐ { σ_Iₐ with nonce := σ_Iₐ.nonce + 1 }
  let pending : PendingCreate :=
    { frame := { fr with exec := evmState }
      stack := stack
      callerAccounts := σ
      value := value
      initOffset := initOffset
      initSize := initSize
      initCodeSize := i.size }
  -- The creation cannot start: the instruction still completes (pushing 0),
  -- with the creator's reserved gas `L(g)` returned untouched.
  let failed : CreateResult :=
    { address := default
      createdAccounts := evmState.createdAccounts
      accounts := σ
      gasRemaining := .ofNat (L evmState.gasAvailable.toNat)
      substate := evmState.toState.substate
      success := false
      output := .empty }
  if σ_Iₐ.nonce.toNat ≥ 2^64-1 then
    return .next (← resumeAfterCreate failed pending).exec
  if value ≤ (σ.find? Iₐ |>.option 0 (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152 then
    return .needsCreate
      { blobVersionedHashes := I.blobVersionedHashes
        createdAccounts := evmState.createdAccounts
        genesisBlockHeader := evmState.genesisBlockHeader
        blocks := evmState.blocks
        accounts := σStar
        originalAccounts := evmState.σ₀
        substate := evmState.toState.substate
        caller := Iₐ
        origin := I.sender
        gas := .ofNat <| L evmState.gasAvailable.toNat
        gasPrice := .ofNat I.gasPrice
        value := value
        initCode := i
        depth := Iₑ + 1
        salt := ζ
        blockHeader := I.header
        canModifyState := I.perm }
      pending
  return .next (← resumeAfterCreate failed pending).exec

local instance : MonadLift Option (Except ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

/--
Execute the (already validated and costed) instruction `instr` on the
frame's state. CALL/CREATE-family instructions suspend the frame instead of
recursing; everything else is `stepPrimop`.
-/
private def execInstr (fr : Frame) (instr : Operation) (arg : Option (UInt256 × Nat))
    (gasCost : ℕ) : Except ExecutionException StepOutcome := do
  match instr with
    | .CREATE =>
      let evmState :=
        { fr.exec with
            execLength := fr.exec.execLength + 1
            gasAvailable := fr.exec.gasAvailable - UInt256.ofNat gasCost }
      match evmState.stack.pop3 with
        | some ⟨stack, μ₀, μ₁, μ₂⟩ =>
          prepareCreate fr evmState stack μ₀ μ₁ μ₂ none
        | _ => .error .StackUnderflow
    | .CREATE2 =>
      -- Exactly equivalent to CREATE except ζ ≡ μₛ[3]
      let evmState :=
        { fr.exec with
            execLength := fr.exec.execLength + 1
            gasAvailable := fr.exec.gasAvailable - UInt256.ofNat gasCost }
      match evmState.stack.pop4 with
        | some ⟨stack, μ₀, μ₁, μ₂, μ₃⟩ =>
          prepareCreate fr evmState stack μ₀ μ₁ μ₂ (some <| Evm.UInt256.toByteArray μ₃)
        | _ => .error .StackUnderflow
    | .CALL => do
      let evmState := { fr.exec with execLength := fr.exec.execLength + 1 }
      -- Names are from the YP, these are:
      -- μ₀ - gas, μ₁ - to, μ₂ - value, μ₃ - inOffset, μ₄ - inSize, μ₅ - outOffset, μ₆ - outSize
      let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
      return prepareCall fr evmState gasCost stack
        μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
        evmState.executionEnv.perm
    | .CALLCODE => do
      let evmState := { fr.exec with execLength := fr.exec.execLength + 1 }
      let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
      return prepareCall fr evmState gasCost stack
        μ₀ (.ofNat evmState.executionEnv.codeOwner) (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
        evmState.executionEnv.perm
    | .DELEGATECALL => do
      -- No `value` argument: the parent's value and caller are inherited.
      let evmState := { fr.exec with execLength := fr.exec.execLength + 1 }
      let (stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop6
      return prepareCall fr evmState gasCost stack
        μ₀ (.ofNat evmState.executionEnv.source) (.ofNat evmState.executionEnv.codeOwner) μ₁ 0 evmState.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆
        evmState.executionEnv.perm
    | .STATICCALL => do
      -- No `value` argument; the child runs with state modification forbidden.
      let evmState := { fr.exec with execLength := fr.exec.execLength + 1 }
      let (stack, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop6
      return prepareCall fr evmState gasCost stack
        μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ 0 0 μ₃ μ₄ μ₅ μ₆
        false
    | instr =>
      let exec' ← stepPrimop instr arg
        { fr.exec with
            execLength := fr.exec.execLength + 1
            gasAvailable := fr.exec.gasAvailable - UInt256.ofNat gasCost }
      return .next exec'

/--
Execute one instruction of the frame: decode at the pc (an out-of-code pc
reads as STOP), run the exceptional-halt checks `Z`, execute, and classify
the result via the normal-halt discriminator `H`.
-/
def stepFrame (fr : Frame) : StepOutcome :=
  let evmState := fr.exec
  let (w, arg) := decode evmState.executionEnv.code evmState.pc |>.getD (.STOP, .none)
  match Z fr.validJumps w evmState with
    | .error e => .halt (.exception e)
    | .ok (evmState, cost₂) =>
      -- Every instruction's net stack effect is exactly `α − δ` (the
      -- StackOverflow check above is predicated on this), so the cached
      -- stack size can be maintained without walking the stack.
      let stackSize' := evmState.stackSize - (δ w).getD 0 + (α w).getD 0
      match execInstr { fr with exec := evmState } w arg cost₂ with
        | .error e => .halt (.exception e)
        | .ok (.next exec') =>
          let exec' := { exec' with stackSize := stackSize' }
          match H exec'.toMachineState w with
            | none => .next exec'
            | some o =>
              if w == .REVERT then
                /-
                  The Yellow Paper says we don't call the "iterator function" "O" for `REVERT`,
                  but we actually have to call the semantics of `REVERT` to pass the test
                  EthereumTests/BlockchainTests/GeneralStateTests/stReturnDataTest/returndatacopy_after_revert_in_staticcall.json
                  And the EEL spec does so too.
                -/
                .halt (.revert exec'.gasAvailable o)
              else
                .halt (.success exec' o)
        | .ok (.needsCall params pending) =>
          -- The suspended frame resumes with the popped stack plus the pushed
          -- success flag — its length is the predicted `α − δ` net effect.
          .needsCall params
            { pending with frame.exec.stackSize := stackSize' }
        | .ok (.needsCreate params pending) =>
          .needsCreate params
            { pending with frame.exec.stackSize := stackSize' }
        | .ok outcome => outcome

end Evm
