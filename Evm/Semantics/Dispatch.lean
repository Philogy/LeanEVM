import Evm.Instr
import Evm.Semantics.Call
import Evm.Semantics.Create
import Evm.Semantics.Decode
import Evm.Semantics.Frame
import Evm.Semantics.PrimOps

/-!
The instruction dispatcher: one central match holding ALL opcode-specific
logic. Each arm pops its operands once, charges its memory-expansion and
operation costs (named formulas from `Evm.Semantics.Gas`), performs its
op-specific validity checks, executes, and emits a `Signal` — continue, halt
(with the payload), or suspend on a child call/create.

The generic preamble (`stepFrame`) handles only what is purely syntactic,
straight from the δ/α arity tables: invalid instructions, stack underflow and
overflow, and the `stackSize`/`execLength` bookkeeping.
-/

namespace Evm

open GasConstants

/--
Shared tail of the CALL-family instructions: charge the memory expansion over
both ranges and `CCALL` (computing the `CCALLGAS` cap exactly once), read the
input data, and either suspend on the child call (`.needsCall`) or — when the
balance/depth pre-checks fail — complete the instruction immediately with a
failed-call result.
-/
private def callArm (fr : Frame) (exec : ExecutionState) (stack : Stack UInt256)
    (gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) : Step := do
  -- The memory expansion spans the input and the output ranges (H.1).
  let m : ℕ := MachineState.M exec.activeWords.toNat inOffset.toNat inSize.toNat
  let words' : UInt256 := .ofNat <| MachineState.M m outOffset.toNat outSize.toNat
  let exec ← charge (Cₘ words' - Cₘ exec.activeWords) exec
  let codeAddress : AccountAddress := AccountAddress.ofUInt256 codeAddress
  let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
  let caller : AccountAddress := AccountAddress.ofUInt256 caller
  let self := exec.executionEnv.address
  let accounts := exec.accounts
  let depth := exec.executionEnv.depth
  -- CCALLGAS/CCALL on the post-memory-charge gas: the cap is computed ONCE,
  -- both for the charge and for the child's allowance.
  let extraCost := callExtraCost codeAddress recipient value accounts exec.substate
  let gasCap := callGasCap codeAddress recipient value gas accounts exec.gasAvailable exec.substate
  let childGas := if value = 0 then gasCap else gasCap + Gcallstipend
  let exec ← charge (gasCap + extraCost) exec
  -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
  let inputData := exec.memory.readWithPadding inOffset.toNat inSize.toNat
  let substate' := exec.addAccessedAccount codeAddress |>.substate
  let pending : PendingCall :=
    { frame := { fr with exec := exec }
      stack := stack
      callerAccounts := accounts
      value := value
      inOffset := inOffset
      inSize := inSize
      outOffset := outOffset
      outSize := outSize }
  if value ≤ (accounts.find? self |>.option 0 (·.balance)) ∧ depth < 1024 then
    .ok <| .needsCall
      { blobVersionedHashes := exec.executionEnv.blobVersionedHashes
        createdAccounts := exec.createdAccounts
        genesisBlockHeader := exec.genesisBlockHeader
        blocks := exec.blocks
        accounts := accounts                                -- accounts in  Θ(accounts, ..)
        originalAccounts := exec.originalAccounts
        substate := substate'                               -- A* in Θ(.., A*, ..)
        caller := caller
        origin := exec.executionEnv.origin                  -- Iₒ in Θ(.., Iₒ, ..)
        recipient := recipient                              -- codeAddress in Θ(.., codeAddress, ..)
        codeSource := toExecute accounts codeAddress
        gas := .ofNat childGas
        gasPrice := .ofNat exec.executionEnv.gasPrice       -- Iₚ in Θ(.., Iₚ, ..)
        value := value
        apparentValue := apparentValue
        calldata := inputData
        depth := depth + 1
        blockHeader := exec.executionEnv.blockHeader
        chainId := exec.executionEnv.chainId
        canModifyState := permission }                      -- I_w in Θ(.., I_W)
      pending
  else
    -- otherwise (σ, CCALLGAS(σ, μ, A), A, 0, ()) — the call never happens;
    -- the child's gas allowance returns to the caller untouched.
    let failed : CallResult :=
      { createdAccounts := exec.createdAccounts
        accounts := accounts
        gasRemaining := .ofNat childGas
        substate := substate'
        success := false
        output := .empty }
    .ok <| .next (resumeAfterCall failed pending).exec

/--
Shared tail of CREATE/CREATE2 (costs already charged): bump the creator's
nonce and either suspend on the init-code execution (`.needsCreate`) or —
when the nonce/balance/depth/init-code-size pre-checks fail — complete the
instruction immediately with a failed-creation result.
-/
private def createArm (fr : Frame) (exec : ExecutionState)
    (stack : Stack UInt256) (value initOffset initSize : UInt256)
    (salt : Option ByteArray) : Step := do
  let initCode := exec.memory.readWithPadding initOffset.toNat initSize.toNat
  let env := exec.executionEnv
  let self := env.address
  let depth := env.depth
  let accounts := exec.accounts
  let selfAccount : Account := accounts.find? self |>.getD default
  let accountsWithBump := accounts.insert self { selfAccount with nonce := selfAccount.nonce + 1 }
  let pending : PendingCreate :=
    { frame := { fr with exec := exec }
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
      createdAccounts := exec.createdAccounts
      accounts := accounts
      gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
      substate := exec.toState.substate
      success := false
      output := .empty }
  if selfAccount.nonce.toNat ≥ 2^64-1 then
    return .next (← resumeAfterCreate failed pending).exec
  if value ≤ (accounts.find? self |>.option 0 (·.balance)) ∧ depth < 1024 ∧ initCode.size ≤ 49152 then
    return .needsCreate
      { blobVersionedHashes := env.blobVersionedHashes
        createdAccounts := exec.createdAccounts
        genesisBlockHeader := exec.genesisBlockHeader
        blocks := exec.blocks
        accounts := accountsWithBump
        originalAccounts := exec.originalAccounts
        substate := exec.toState.substate
        caller := self
        origin := env.origin
        gas := .ofNat <| allButOneSixtyFourth exec.gasAvailable.toNat
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

/--
THE dispatcher match: one arm per opcode, holding everything specific to it —
operand pops, gas charges (named Appendix G formulas with the popped operands),
validity checks, semantics, and the emitted `Signal`.
-/
def dispatch (op : Operation) (arg : Option (UInt256 × Nat)) (fr : Frame)
    (exec : ExecutionState) : Step :=
  match op with
    -- ## Halting instructions (the YP's `H` cases, emitted directly)
    | .STOP => .ok <| .halted (.success exec .empty)
    | .RETURN | .REVERT => do
      -- Halt carrying m[μs[0] ... (μs[0] + μs[1] − 1)].
      let (stack, offset, size) ← exec.stack.pop2
      let exec ← chargeMemExpansion exec offset.toNat size.toNat
      let output := exec.memory.readWithPadding offset.toNat size.toNat
      let machine :=
        { exec.toMachineState with
            activeWords := .ofNat <| MachineState.M exec.activeWords.toNat offset.toNat size.toNat }
      let exec := ExecutionState.replaceStackAndIncrPC { exec with toMachineState := machine } stack
      if op = .REVERT then
        /-
          The Yellow Paper says we don't call the "iterator function" "O" for `REVERT`,
          but we actually have to run the semantics of `REVERT` (memory read and
          activeWords expansion) to pass the test
          EthereumTests/BlockchainTests/GeneralStateTests/stReturnDataTest/returndatacopy_after_revert_in_staticcall.json
          And the EEL spec does so too.
        -/
        return .halted (.revert exec.gasAvailable output)
      else
        return .halted (.success exec output)
    | .SELFDESTRUCT => do
      requireStateMod exec
      let (stack, recipientWord) ← exec.stack.pop
      let self := exec.executionEnv.address
      let r : AccountAddress := AccountAddress.ofUInt256 recipientWord
      let warm := exec.substate.accessedAccounts.contains r
      let createsAccount :=
        Evm.State.dead exec.accounts r ∧ (exec.accounts.find? self |>.option 0 (·.balance)) ≠ 0
      let exec ← charge (selfdestructCost warm createsAccount) exec
      let exec' :=
        if exec.createdAccounts.contains self then
          -- When `SELFDESTRUCT` is executed in the same transaction as the contract was created
          let substate' : Substate :=
            { exec.substate with
                selfDestructSet := exec.substate.selfDestructSet.insert self
                accessedAccounts := exec.substate.accessedAccounts.insert r }
          let accountMap' :=
            match exec.lookupAccount self with
              | none =>
                dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; exec.accounts
              | some selfAccount  =>
                match exec.lookupAccount r with
                  | none =>
                    if selfAccount.balance == 0 then
                      exec.accounts
                    else
                      exec.accounts.insert r
                        {(default : Account) with balance := selfAccount.balance}
                          |>.insert self {selfAccount with balance := 0}
                  | some recipientAccount =>
                    if r ≠ self then
                      exec.accounts.insert r
                        {recipientAccount with balance := recipientAccount.balance + selfAccount.balance}
                          |>.insert self {selfAccount with balance := 0}
                    else
                      -- if the target is the same as the contract calling `SELFDESTRUCT` that Ether will be burnt.
                      exec.accounts.insert r {recipientAccount with balance := 0}
                        |>.insert self {selfAccount with balance := 0}
          { exec with accounts := accountMap', substate := substate' }
        else
          /- When SELFDESTRUCT is executed in a transaction that is not the
            same as the contract calling SELFDESTRUCT was created:
          -/
          let substate' : Substate :=
            { exec.substate with
                accessedAccounts := exec.substate.accessedAccounts.insert r }
          let accountMap' :=
            match exec.lookupAccount self with
              | none => dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; exec.accounts
              | some selfAccount  =>
                match exec.lookupAccount r with
                  | none =>
                    if selfAccount.balance == 0 then
                      exec.accounts
                    else
                      exec.accounts.insert r
                        {(default : Account) with balance := selfAccount.balance}
                          |>.insert self {selfAccount with balance := 0}
                  | some recipientAccount =>
                    if r ≠ self then
                      exec.accounts.insert r
                        {recipientAccount with balance := recipientAccount.balance + selfAccount.balance}
                          |>.insert self {selfAccount with balance := 0}
                    else
                      -- Note that if the target is the same as the contract
                      -- calling SELFDESTRUCT there is no net change in balances.
                      -- Unlike the prior specification, Ether will not be burnt in this case.
                      exec.accounts
          { exec with accounts := accountMap', substate := substate' }
      return .halted (.success (exec'.replaceStackAndIncrPC stack) .empty)

    -- ## Calls and creates (suspend the frame)
    | .CALL => do
      let (stack, gas, toAddress, value, inOffset, inSize, outOffset, outSize) ← exec.stack.pop7
      -- A value-bearing CALL is in the state-mutating set `W` (eq. 159).
      if value ≠ 0 ∧ ¬ exec.executionEnv.canModifyState then throw .StaticModeViolation
      callArm fr exec stack
        gas (.ofNat exec.executionEnv.address) toAddress toAddress value value inOffset inSize outOffset outSize
        exec.executionEnv.canModifyState
    | .CALLCODE => do
      let (stack, gas, toAddress, value, inOffset, inSize, outOffset, outSize) ← exec.stack.pop7
      callArm fr exec stack
        gas (.ofNat exec.executionEnv.address) (.ofNat exec.executionEnv.address) toAddress value value inOffset inSize outOffset outSize
        exec.executionEnv.canModifyState
    | .DELEGATECALL => do
      -- No `value` argument: the parent's value and caller are inherited.
      let (stack, gas, toAddress, inOffset, inSize, outOffset, outSize) ← exec.stack.pop6
      callArm fr exec stack
        gas (.ofNat exec.executionEnv.caller) (.ofNat exec.executionEnv.address) toAddress 0 exec.executionEnv.value inOffset inSize outOffset outSize
        exec.executionEnv.canModifyState
    | .STATICCALL => do
      -- No `value` argument; the child runs with state modification forbidden.
      let (stack, gas, toAddress, inOffset, inSize, outOffset, outSize) ← exec.stack.pop6
      callArm fr exec stack
        gas (.ofNat exec.executionEnv.address) toAddress toAddress 0 0 inOffset inSize outOffset outSize
        false
    | .CREATE => do
      requireStateMod exec
      let (stack, value, initOffset, initSize) ← exec.stack.pop3
      if initSize > 49152 then throw .OutOfGass -- EIP-3860
      let exec ← chargeMemExpansion exec initOffset.toNat initSize.toNat
      let exec ← charge (createCost initSize) exec
      createArm fr exec stack value initOffset initSize none
    | .CREATE2 => do
      -- Exactly equivalent to CREATE except ζ ≡ μₛ[3]
      requireStateMod exec
      let (stack, value, initOffset, initSize, salt) ← exec.stack.pop4
      if initSize > 49152 then throw .OutOfGass -- EIP-3860
      let exec ← chargeMemExpansion exec initOffset.toNat initSize.toNat
      let exec ← charge (create2Cost initSize) exec
      createArm fr exec stack value initOffset initSize (some <| Evm.UInt256.toByteArray salt)

    -- ## Arithmetic, comparison, bitwise
    | .ADD => binOp UInt256.add exec
    | .MUL => binOp UInt256.mul exec Glow
    | .SUB => binOp UInt256.sub exec
    | .DIV => binOp UInt256.div exec Glow
    | .SDIV => binOp UInt256.sdiv exec Glow
    | .MOD => binOp UInt256.mod exec Glow
    | .SMOD => binOp UInt256.smod exec Glow
    | .ADDMOD => ternOp UInt256.addMod exec Gmid
    | .MULMOD => ternOp UInt256.mulMod exec Gmid
    | .EXP => do
      let (stack, base, exponent) ← exec.stack.pop2
      let exec ← charge (expCost exponent) exec
      continueWith <| exec.replaceStackAndIncrPC (stack.push (UInt256.exp base exponent))
    | .SIGNEXTEND => binOp UInt256.signextend exec Glow
    | .LT => binOp UInt256.lt exec
    | .GT => binOp UInt256.gt exec
    | .SLT => binOp UInt256.slt exec
    | .SGT => binOp UInt256.sgt exec
    | .EQ => binOp UInt256.eq exec
    | .ISZERO => unOp UInt256.isZero exec
    | .AND => binOp UInt256.land exec
    | .OR => binOp UInt256.lor exec
    | .XOR => binOp UInt256.xor exec
    | .NOT => unOp UInt256.lnot exec
    | .BYTE => binOp UInt256.byteAt exec
    | .SHL => binOp (flip UInt256.shiftLeft) exec
    | .SHR => binOp (flip UInt256.shiftRight) exec
    | .SAR => binOp UInt256.sar exec

    | .KECCAK256 => do
      let (stack, offset, size) ← exec.stack.pop2
      let exec ← chargeMemExpansion exec offset.toNat size.toNat
      let exec ← charge (keccakCost size) exec
      let (v, machine') := exec.toMachineState.keccak256 offset size
      continueWith <| ExecutionState.replaceStackAndIncrPC { exec with toMachineState := machine' } (stack.push v)

    -- ## Environment and world-state readers
    | .ADDRESS => pushOp (λ s ↦ .ofNat s.executionEnv.address.val) exec
    | .BALANCE => unStateOp Evm.State.balance (λ s a ↦ accessCost (AccountAddress.ofUInt256 a) s.substate) exec
    | .ORIGIN => pushOp (λ s ↦ .ofNat s.executionEnv.origin.val) exec
    | .CALLER => pushOp (λ s ↦ .ofNat s.executionEnv.caller.val) exec
    | .CALLVALUE => pushOp (λ s ↦ s.executionEnv.value) exec
    | .CALLDATALOAD => unStateOp (λ s v ↦ (s, Evm.State.calldataload s v)) (λ _ _ ↦ Gverylow) exec
    | .CALLDATASIZE => pushOp (λ s ↦ .ofNat s.executionEnv.calldata.size) exec
    | .CODESIZE => pushOp (λ s ↦ .ofNat s.executionEnv.code.size) exec
    | .GASPRICE => pushOp (λ s ↦ .ofNat s.executionEnv.gasPrice) exec
    | .EXTCODESIZE => unStateOp Evm.State.extCodeSize (λ s a ↦ accessCost (AccountAddress.ofUInt256 a) s.substate) exec
    | .EXTCODEHASH => unStateOp Evm.State.extCodeHash (λ s a ↦ accessCost (AccountAddress.ofUInt256 a) s.substate) exec
    | .RETURNDATASIZE => pushOp (λ s ↦ .ofNat s.returnData.size) exec
    | .BLOCKHASH => unStateOp (λ s v ↦ (s, Evm.State.blockHash s v)) (λ _ _ ↦ Gblockhash) exec
    | .COINBASE => pushOp (λ s ↦ .ofNat (Evm.State.coinBase s.toState).val) exec
    | .TIMESTAMP => pushOp (λ s ↦ Evm.State.timeStamp s.toState) exec
    | .NUMBER => pushOp (λ s ↦ Evm.State.number s.toState) exec
    -- "RANDAO is a pseudorandom value generated by validators on the Ethereum consensus layer"
    -- "the details of generating the RANDAO value on the Beacon Chain is beyond the scope of this paper"
    | .PREVRANDAO => pushOp (λ s ↦ Evm.prevRandao s.executionEnv) exec
    | .GASLIMIT => pushOp (λ s ↦ Evm.State.gasLimit s.toState) exec
    | .CHAINID => pushOp (λ s ↦ Evm.State.chainId s.toState) exec
    | .SELFBALANCE => pushOp (λ s ↦ Evm.State.selfbalance s.toState) exec Glow
    | .BASEFEE => pushOp (λ s ↦ Evm.basefee s.executionEnv) exec
    | .BLOBHASH => do
      let (stack, i) ← exec.stack.pop
      let exec ← charge HASH_OPCODE_GAS exec
      continueWith <| exec.replaceStackAndIncrPC (stack.push (blobhash exec.executionEnv i))
    | .BLOBBASEFEE => pushOp (λ s ↦ s.executionEnv.getBlobGasprice) exec

    -- ## Copies
    | .CALLDATACOPY => do
      let (stack, mstart, dstart, size) ← exec.stack.pop3
      let exec ← chargeMemExpansion exec mstart.toNat size.toNat
      let exec ← charge (Gverylow + copyCost size) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toSharedState := exec.toSharedState.calldatacopy mstart dstart size } stack
    | .CODECOPY => do
      let (stack, mstart, cstart, size) ← exec.stack.pop3
      let exec ← chargeMemExpansion exec mstart.toNat size.toNat
      let exec ← charge (Gverylow + copyCost size) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toSharedState := exec.toSharedState.codeCopy mstart cstart size } stack
    | .EXTCODECOPY => do
      let (stack, addr, mstart, cstart, size) ← exec.stack.pop4
      let exec ← chargeMemExpansion exec mstart.toNat size.toNat
      let exec ← charge (accessCost (AccountAddress.ofUInt256 addr) exec.substate + copyCost size) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toSharedState := exec.toSharedState.extCodeCopy' addr mstart cstart size } stack
    | .RETURNDATACOPY => do
      let (stack, mstart, rstart, size) ← exec.stack.pop3
      if rstart.toNat + size.toNat > exec.returnData.size then throw .InvalidMemoryAccess
      let exec ← chargeMemExpansion exec mstart.toNat size.toNat
      let exec ← charge (Gverylow + copyCost size) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toMachineState := exec.toMachineState.returndatacopy mstart rstart size } stack
    | .MCOPY => do
      let (stack, dest, src, size) ← exec.stack.pop3
      let exec ← chargeMemExpansion exec (max dest.toNat src.toNat) size.toNat
      let exec ← charge (Gverylow + copyCost size) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toMachineState := exec.toMachineState.mcopy dest src size } stack

    -- ## Stack, memory, storage
    | .POP => do
      let exec ← charge Gbase exec
      let (stack, _) ← exec.stack.pop
      continueWith <| exec.replaceStackAndIncrPC stack
    | .MLOAD => do
      let (stack, addr) ← exec.stack.pop
      let exec ← chargeMemExpansion exec addr.toNat 32
      let exec ← charge Gverylow exec
      let (v, machine') := exec.toMachineState.mload addr
      continueWith <| ExecutionState.replaceStackAndIncrPC { exec with toMachineState := machine' } (stack.push v)
    | .MSTORE => do
      let (stack, addr, val) ← exec.stack.pop2
      let exec ← chargeMemExpansion exec addr.toNat 32
      let exec ← charge Gverylow exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toMachineState := exec.toMachineState.mstore addr val } stack
    | .MSTORE8 => do
      let (stack, addr, val) ← exec.stack.pop2
      let exec ← chargeMemExpansion exec addr.toNat 1
      let exec ← charge Gverylow exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toMachineState := exec.toMachineState.mstore8 addr val } stack
    | .SLOAD =>
      unStateOp Evm.State.sload
        (λ s key ↦ sloadCost (s.substate.accessedStorageKeys.contains (s.executionEnv.address, key))) exec
    | .SSTORE => do
      requireStateMod exec
      -- The EIP-2200 stipend check, on the gas available BEFORE the charge.
      if exec.gasAvailable.toNat ≤ Gcallstipend then throw .OutOfGass
      let (stack, key, newValue) ← exec.stack.pop2
      let self := exec.executionEnv.address
      let originalValue := exec.originalAccounts.find? self |>.option 0 (·.storage.findD key 0)
      let currentValue := exec.accounts.find? self |>.option 0 (·.storage.findD key 0)
      let warm := exec.substate.accessedStorageKeys.contains (self, key)
      let exec ← charge (sstoreCost originalValue currentValue newValue warm) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toState := exec.toState.sstore key newValue } stack
    | .TLOAD => unStateOp Evm.State.tload (λ _ _ ↦ tloadCost) exec
    | .TSTORE => do
      requireStateMod exec
      let exec ← charge tstoreCost exec
      let (stack, key, val) ← exec.stack.pop2
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toState := exec.toState.tstore key val } stack
    | .MSIZE => pushOp (λ s ↦ s.toMachineState.msize) exec
    | .GAS => pushOp (λ s ↦ s.gasAvailable) exec

    -- ## Logs
    | .LOG0 => do
      let (stack, offset, size) ← exec.stack.pop2
      logArm exec stack offset size #[]
    | .LOG1 => do
      let (stack, offset, size, t₁) ← exec.stack.pop3
      logArm exec stack offset size #[t₁]
    | .LOG2 => do
      let (stack, offset, size, t₁, t₂) ← exec.stack.pop4
      logArm exec stack offset size #[t₁, t₂]
    | .LOG3 => do
      let (stack, offset, size, t₁, t₂, t₃) ← exec.stack.pop5
      logArm exec stack offset size #[t₁, t₂, t₃]
    | .LOG4 => do
      let (stack, offset, size, t₁, t₂, t₃, t₄) ← exec.stack.pop6
      logArm exec stack offset size #[t₁, t₂, t₃, t₄]

    -- ## Control flow
    | .JUMP => do
      let exec ← charge Gmid exec
      let (stack, dest) ← exec.stack.pop
      if fr.validJumps.contains dest then
        continueWith { exec with pc := dest, stack := stack }
      else
        throw .BadJumpDestination
    | .JUMPI => do
      let exec ← charge Ghigh exec
      let (stack, dest, cond) ← exec.stack.pop2
      if cond != 0 then
        if fr.validJumps.contains dest then
          continueWith { exec with pc := dest, stack := stack }
        else
          throw .BadJumpDestination
      else
        continueWith { exec with pc := exec.pc + 1, stack := stack }
    | .PC => pushOp (λ s ↦ s.pc) exec
    | .JUMPDEST => do
      let exec ← charge Gjumpdest exec
      continueWith exec.incrPC

    -- ## Pushes, dups, swaps
    | .Push .PUSH0 => do
      let exec ← charge Gbase exec
      continueWith <| exec.replaceStackAndIncrPC (exec.stack.push 0)
    | .Push _ => do
      let exec ← charge Gverylow exec
      let some (argVal, argWidth) := arg | throw .StackUnderflow
      continueWith <| exec.replaceStackAndIncrPC (exec.stack.push argVal) (pcΔ := argWidth.succ)
    | .Dup d => dup ((serializeDupInstr d).toNat - 0x7f) exec
    | .Exchange e => swap ((serializeSwapInstr e).toNat - 0x8f) exec

    | _ => throw .InvalidInstruction

/--
Execute one instruction of the frame: decode at the pc (an out-of-code pc
reads as STOP), run the purely syntactic preamble checks straight off the
δ/α arity tables (invalid instruction, stack underflow/overflow), maintain
the `stackSize`/`execLength` bookkeeping, and dispatch.
-/
def stepFrame (fr : Frame) : Signal :=
  let exec := fr.exec
  let (op, arg) := decode exec.executionEnv.code exec.pc |>.getD (.STOP, .none)
  match stackPopCount op, stackPushCount op with
    | some δ, some α =>
      if exec.stackSize < δ then
        .halted (.exception .StackUnderflow)
      else if exec.stackSize - δ + α > 1024 then
        .halted (.exception .StackOverflow)
      else
        -- Every instruction's net stack effect is exactly `α − δ` (the
        -- overflow check above is predicated on this), so the cached stack
        -- size can be maintained without walking the stack.
        let exec :=
          { exec with
              execLength := exec.execLength + 1
              stackSize := exec.stackSize - δ + α }
        match dispatch op arg fr exec with
          | .ok signal => signal
          | .error e => .halted (.exception e)
    | _, _ => .halted (.exception .InvalidInstruction)

end Evm
