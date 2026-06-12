import Evm.Semantics.Gas
import Evm.Semantics.GasConstants
import Evm.Semantics.Call
import Evm.Semantics.Create
import Evm.Semantics.Decode
import Evm.Semantics.Frame
import Evm.Semantics.Instructions

namespace Evm

/--
The state-modifying instructions `W` (eq. 159) — forbidden when the frame
lacks `perm` (static call context).
-/
private def mutatesState (w : Operation) (s : Stack UInt256) : Bool :=
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
private def checkExceptionalHalt (validJumps : Array UInt256) (w : Operation) (evmState : ExecutionState) :
    Except ExecutionException (ExecutionState × ℕ) := do
  -- The stack-depth check precedes the cost computations: both
  -- memoryExpansionCost and operationCost peek at stack slots with `!`.
  if stackPopCount w = none then
    .error .InvalidInstruction
  if evmState.stackSize < (stackPopCount w).getD 0 then
    .error .StackUnderflow
  let cost₁ := memoryExpansionCost evmState w
  if evmState.gasAvailable.toNat < cost₁ then
    .error .OutOfGass
  let gasAvailable := evmState.gasAvailable - .ofNat cost₁
  let evmState := { evmState with gasAvailable := gasAvailable }
  let cost₂ := operationCost evmState w

  if evmState.gasAvailable.toNat < cost₂ then
    .error .OutOfGass

  let invalidJump := notIn evmState.stack[0]? validJumps

  if w = .JUMP ∧ invalidJump then
    .error .BadJumpDestination

  if w = .JUMPI ∧ (evmState.stack[1]? ≠ some 0) ∧ invalidJump then
    .error .BadJumpDestination

  if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 0).toNat + (evmState.stack.getD 2 0).toNat > evmState.returnData.size then
    .error .InvalidMemoryAccess

  if evmState.stackSize - (stackPopCount w).getD 0 + (stackPushCount w).getD 0 > 1024 then
    .error .StackOverflow

  if (¬ evmState.executionEnv.canModifyState) ∧ mutatesState w evmState.stack then
    .error .StaticModeViolation

  if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
    .error .OutOfGass

  if
    w.isCreate ∧ evmState.stack.getD 2 0 > 49152
  then
    .error .OutOfGass

  pure (evmState, cost₂)

/--
Shared tail of the CALL-family instructions: compute the child's gas
allowance, charge the instruction cost, read the input data, and either
suspend on the child call (`.needsCall`) or — when the balance/depth
pre-checks fail — complete the instruction immediately with a failed-call
result.
-/
private def prepareCall (fr : Frame) (evmState : ExecutionState) (gasCost : ℕ)
    (stack : Stack UInt256)
    (gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) : Signal :=
  let codeAddress : AccountAddress := AccountAddress.ofUInt256 codeAddress
  let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
  let caller : AccountAddress := AccountAddress.ofUInt256 caller
  let self := evmState.executionEnv.address
  let accounts := evmState.accounts
  let depth := evmState.executionEnv.depth
  let callgas := callGas codeAddress recipient value gas accounts evmState.toMachineState evmState.substate
  let evmState := { evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost }
  -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
  let inputData := evmState.memory.readWithPadding inOffset.toNat inSize.toNat
  let substate' := evmState.addAccessedAccount codeAddress |>.substate
  let pending : PendingCall :=
    { frame := { fr with exec := evmState }
      stack := stack
      callerAccounts := accounts
      value := value
      inOffset := inOffset
      inSize := inSize
      outOffset := outOffset
      outSize := outSize }
  if value ≤ (accounts.find? self |>.option 0 (·.balance)) ∧ depth < 1024 then
    .needsCall
      { blobVersionedHashes := evmState.executionEnv.blobVersionedHashes
        createdAccounts := evmState.createdAccounts
        genesisBlockHeader := evmState.genesisBlockHeader
        blocks := evmState.blocks
        accounts := accounts                                       -- accounts in  Θ(accounts, ..)
        originalAccounts := evmState.originalAccounts
        substate := substate'                                      -- A* in Θ(.., A*, ..)
        caller := caller
        origin := evmState.executionEnv.origin              -- Iₒ in Θ(.., Iₒ, ..)
        recipient := recipient                              -- codeAddress in Θ(.., codeAddress, ..)
        codeSource := toExecute accounts codeAddress
        gas := .ofNat callgas
        gasPrice := .ofNat evmState.executionEnv.gasPrice   -- Iₚ in Θ(.., Iₚ, ..)
        value := value
        apparentValue := apparentValue
        calldata := inputData
        depth := depth + 1
        blockHeader := evmState.executionEnv.blockHeader
        chainId := evmState.executionEnv.chainId
        canModifyState := permission }                      -- I_w in Θ(.., I_W)
      pending
  else
    -- otherwise (σ, CCALLGAS(σ, μ, A), A, 0, ()) — the call never happens;
    -- the child's gas allowance returns to the caller untouched.
    let failed : CallResult :=
      { createdAccounts := evmState.createdAccounts
        accounts := accounts
        gasRemaining := .ofNat callgas
        substate := substate'
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
    (salt : Option ByteArray) : Except ExecutionException Signal := do
  let initCode := evmState.memory.readWithPadding initOffset.toNat initSize.toNat
  let env := evmState.executionEnv
  let self := env.address
  let depth := env.depth
  let accounts := evmState.accounts
  let selfAccount : Account := accounts.find? self |>.getD default
  let accountsWithBump := accounts.insert self { selfAccount with nonce := selfAccount.nonce + 1 }
  let pending : PendingCreate :=
    { frame := { fr with exec := evmState }
      stack := stack
      callerAccounts := accounts
      value := value
      initOffset := initOffset
      initSize := initSize
      initCodeSize := initCode.size }
  -- The creation cannot start: the instruction still completes (pushing 0),
  -- with the creator's reserved gas `allButOneSixtyFourth(g)` returned untouched.
  let failed : CreateResult :=
    { address := default
      createdAccounts := evmState.createdAccounts
      accounts := accounts
      gasRemaining := .ofNat (allButOneSixtyFourth evmState.gasAvailable.toNat)
      substate := evmState.toState.substate
      success := false
      output := .empty }
  if selfAccount.nonce.toNat ≥ 2^64-1 then
    return .next (← resumeAfterCreate failed pending).exec
  if value ≤ (accounts.find? self |>.option 0 (·.balance)) ∧ depth < 1024 ∧ initCode.size ≤ 49152 then
    return .needsCreate
      { blobVersionedHashes := env.blobVersionedHashes
        createdAccounts := evmState.createdAccounts
        genesisBlockHeader := evmState.genesisBlockHeader
        blocks := evmState.blocks
        accounts := accountsWithBump
        originalAccounts := evmState.originalAccounts
        substate := evmState.toState.substate
        caller := self
        origin := env.origin
        gas := .ofNat <| allButOneSixtyFourth evmState.gasAvailable.toNat
        gasPrice := .ofNat env.gasPrice
        value := value
        initCode := initCode
        depth := depth + 1
        salt := salt
        blockHeader := env.blockHeader
        chainId := env.chainId
        canModifyState := env.canModifyState }
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
    (gasCost : ℕ) : Except ExecutionException Signal := do
  match instr with
    | .STOP | .SELFDESTRUCT =>
      -- Normal halt with empty output (the YP's `H` cases without a payload).
      let exec' ← stepPrimop instr arg
        { fr.exec with
            execLength := fr.exec.execLength + 1
            gasAvailable := fr.exec.gasAvailable - UInt256.ofNat gasCost }
      return .halted (.success exec' .empty)
    | .RETURN | .REVERT =>
      -- Normal halt / revert carrying m[μs[0] ... (μs[0] + μs[1] − 1)].
      let evmState :=
        { fr.exec with
            execLength := fr.exec.execLength + 1
            gasAvailable := fr.exec.gasAvailable - UInt256.ofNat gasCost }
      let (stack, offset, size) ← evmState.stack.pop2
      let output := evmState.memory.readWithPadding offset.toNat size.toNat
      let machine :=
        { evmState.toMachineState with
            activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat offset.toNat size.toNat }
      let exec' := { evmState with toMachineState := machine }.replaceStackAndIncrPC stack
      if instr = .REVERT then
        /-
          The Yellow Paper says we don't call the "iterator function" "O" for `REVERT`,
          but we actually have to run the semantics of `REVERT` (memory read and
          activeWords expansion) to pass the test
          EthereumTests/BlockchainTests/GeneralStateTests/stReturnDataTest/returndatacopy_after_revert_in_staticcall.json
          And the EEL spec does so too.
        -/
        return .halted (.revert exec'.gasAvailable output)
      else
        return .halted (.success exec' output)
    | .CREATE =>
      let evmState :=
        { fr.exec with
            execLength := fr.exec.execLength + 1
            gasAvailable := fr.exec.gasAvailable - UInt256.ofNat gasCost }
      match evmState.stack.pop3 with
        | some ⟨stack, value, initOffset, initSize⟩ =>
          prepareCreate fr evmState stack value initOffset initSize none
        | _ => .error .StackUnderflow
    | .CREATE2 =>
      -- Exactly equivalent to CREATE except ζ ≡ μₛ[3]
      let evmState :=
        { fr.exec with
            execLength := fr.exec.execLength + 1
            gasAvailable := fr.exec.gasAvailable - UInt256.ofNat gasCost }
      match evmState.stack.pop4 with
        | some ⟨stack, value, initOffset, initSize, salt⟩ =>
          prepareCreate fr evmState stack value initOffset initSize (some <| Evm.UInt256.toByteArray salt)
        | _ => .error .StackUnderflow
    | .CALL => do
      let evmState := { fr.exec with execLength := fr.exec.execLength + 1 }
      let (stack, gas, toAddress, value, inOffset, inSize, outOffset, outSize) ← evmState.stack.pop7
      return prepareCall fr evmState gasCost stack
        gas (.ofNat evmState.executionEnv.address) toAddress toAddress value value inOffset inSize outOffset outSize
        evmState.executionEnv.canModifyState
    | .CALLCODE => do
      let evmState := { fr.exec with execLength := fr.exec.execLength + 1 }
      let (stack, gas, toAddress, value, inOffset, inSize, outOffset, outSize) ← evmState.stack.pop7
      return prepareCall fr evmState gasCost stack
        gas (.ofNat evmState.executionEnv.address) (.ofNat evmState.executionEnv.address) toAddress value value inOffset inSize outOffset outSize
        evmState.executionEnv.canModifyState
    | .DELEGATECALL => do
      -- No `value` argument: the parent's value and caller are inherited.
      let evmState := { fr.exec with execLength := fr.exec.execLength + 1 }
      let (stack, gas, toAddress, inOffset, inSize, outOffset, outSize) ← evmState.stack.pop6
      return prepareCall fr evmState gasCost stack
        gas (.ofNat evmState.executionEnv.caller) (.ofNat evmState.executionEnv.address) toAddress 0 evmState.executionEnv.value inOffset inSize outOffset outSize
        evmState.executionEnv.canModifyState
    | .STATICCALL => do
      -- No `value` argument; the child runs with state modification forbidden.
      let evmState := { fr.exec with execLength := fr.exec.execLength + 1 }
      let (stack, gas, toAddress, inOffset, inSize, outOffset, outSize) ← evmState.stack.pop6
      return prepareCall fr evmState gasCost stack
        gas (.ofNat evmState.executionEnv.address) toAddress toAddress 0 0 inOffset inSize outOffset outSize
        false
    | instr =>
      let exec' ← stepPrimop instr arg
        { fr.exec with
            execLength := fr.exec.execLength + 1
            gasAvailable := fr.exec.gasAvailable - UInt256.ofNat gasCost }
      return .next exec'

/--
Execute one instruction of the frame: decode at the pc (an out-of-code pc
reads as STOP), run the exceptional-halt checks `Z`, and execute. Halting
instructions signal `.halted` (with their payload) directly from `execInstr`.
-/
def stepFrame (fr : Frame) : Signal :=
  let evmState := fr.exec
  let (w, arg) := decode evmState.executionEnv.code evmState.pc |>.getD (.STOP, .none)
  match checkExceptionalHalt fr.validJumps w evmState with
    | .error e => .halted (.exception e)
    | .ok (evmState, cost₂) =>
      -- Every instruction's net stack effect is exactly `α − δ` (stackPushCount − stackPopCount) (the
      -- StackOverflow check above is predicated on this), so the cached
      -- stack size can be maintained without walking the stack.
      let stackSize' := evmState.stackSize - (stackPopCount w).getD 0 + (stackPushCount w).getD 0
      match execInstr { fr with exec := evmState } w arg cost₂ with
        | .error e => .halted (.exception e)
        | .ok (.next exec') =>
          .next { exec' with stackSize := stackSize' }
        | .ok (.needsCall params pending) =>
          -- The suspended frame resumes with the popped stack plus the pushed
          -- success flag — its length is the predicted `α − δ` (stackPushCount − stackPopCount) net effect.
          .needsCall params
            { pending with frame.exec.stackSize := stackSize' }
        | .ok (.needsCreate params pending) =>
          .needsCreate params
            { pending with frame.exec.stackSize := stackSize' }
        | .ok outcome => outcome

end Evm
