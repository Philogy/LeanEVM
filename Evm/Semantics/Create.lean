import Evm.Rlp
import Evm.Machine.ExecutionStateOps
import Evm.Semantics.Gas
import Evm.Semantics.GasConstants
import Evm.Machine.MachineStateOps
import Evm.Semantics.Decode
import Evm.Semantics.Frame
import Evm.Semantics.Params
import Evm.Crypto.Keccak256

namespace Evm

/-- The address-derivation preimage `L_A` (eq. 96). -/
private def contractAddressBytes (creator : AccountAddress) (creatorNonce : UInt256) (salt : Option ByteArray) (initCode : ByteArray) :
  Option ByteArray
:=
  let creator := creator.toByteArray
  let creatorNonce := BE creatorNonce.toNat
  match salt with
    | none   => Rlp.encode <| .list [.bytes creator, .bytes creatorNonce]
    | some salt => .some <| BE 255 ++ creator ++ salt ++ ffi.KEC initCode

/--
Enter a contract creation — the YP's `Λ` (eq. 93) up to the recursive code
execution: address derivation (eq. 94–96), the EIP-7610 occupied-address
check, account initialisation (eq. 97–99), and execution-environment
construction.
-/
def beginCreate (params : CreateParams) : Except ExecutionException Frame := do
  let accounts := params.accounts
  let creator := params.caller

  -- EIP-3860 (includes EIP-170)
  -- https://eips.ethereum.org/EIPS/eip-3860

  let creatorNonce : UInt256 := (accounts.find? creator |>.option 0 (·.nonce)) - 1
  let some addressPreimage := contractAddressBytes creator creatorNonce params.salt params.initCode | .error .StackUnderflow
  let newAddress : AccountAddress := -- (94) (95)
    (ffi.KEC addressPreimage).extract 12 32 /- 160 bits = 20 bytes -/
      |> fromByteArrayBigEndian |> Fin.ofNat _

  -- A* (97)
  let substateWithNew := params.substate.addAccessedAccount newAddress
  -- σ* (99)
  let existentAccount := accounts.findD newAddress default

  /-
    https://eips.ethereum.org/EIPS/eip-7610
    If a contract creation is attempted due to a creation transaction,
    the CREATE opcode, the CREATE2 opcode, or any other reason,
    and the destination address already has either a nonzero nonce,
    a nonzero code length, or non-empty storage, then the creation MUST throw
    as if the first byte in the init code were an invalid opcode.
  -/
  let (initCode, createdAccounts) :=
    if
      existentAccount.nonce ≠ 0
        || existentAccount.code.size ≠ 0
        || existentAccount.storage != default
    then
      (⟨#[0xfe]⟩, params.createdAccounts)
    else (params.initCode, params.createdAccounts.insert newAddress)

  let newAccount : Account :=
    { existentAccount with
        nonce := existentAccount.nonce + 1
        balance := params.value + existentAccount.balance
    }

  -- If `value` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let accountsWithNew :=
    match accounts.find? creator with
      | none => accounts
      | some ac =>
        accounts.insert creator { ac with balance := ac.balance - params.value }
          |>.insert newAddress newAccount -- (99)
  let env : ExecutionEnv :=
    { address := newAddress
    , origin    := params.origin
    , caller    := creator
    , value  := params.value
    , calldata  := default
    , code      := initCode
    , gasPrice  := params.gasPrice.toNat
    , blockHeader := params.blockHeader
    , depth     := params.depth
    , canModifyState      := params.canModifyState
    , blobVersionedHashes := params.blobVersionedHashes
    , chainId   := params.chainId
    }
  .ok
    { kind := .create newAddress ⟨createdAccounts, accounts, substateWithNew⟩
      validJumps := validJumpDests initCode 0
      exec :=
        { (default : ExecutionState) with
            accounts := accountsWithNew
            originalAccounts := params.originalAccounts
            executionEnv := env
            substate := substateWithNew
            createdAccounts := createdAccounts
            gasAvailable := params.gas
            blocks := params.blocks
            genesisBlockHeader := params.genesisBlockHeader } }

/--
Finish a contract creation — the YP's `Λ` after init-code execution: charge
the code-deposit cost (eq. 113–114), run the failure checks `F` (eq. 118 —
occupied address, unaffordable deposit, EIP-170 size, EIP-3541 `0xef`), and
either store the code or roll back to the checkpoint (eq. 115–117).
-/
def endCreate (address : AccountAddress) (checkpoint : Checkpoint) : FrameHalt → CreateResult
  | .success exec returnedData =>
    -- The code-deposit cost (113)
    let depositCost := GasConstants.Gcodedeposit * returnedData.size

    let deploymentFailed : Bool := Id.run do -- (118)
      let addressOccupied : Bool :=
        match checkpoint.accounts.find? address with
        | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ 0
        | .none => false
      let cannotAffordDeposit : Bool := exec.gasAvailable.toNat < depositCost
      let MAX_CODE_SIZE := 24576
      let codeTooLong : Bool := returnedData.size > MAX_CODE_SIZE
      let startsWith0xef : Bool := ¬codeTooLong && returnedData[0]? = some 0xef
      pure (addressOccupied ∨ cannotAffordDeposit ∨ codeTooLong ∨ startsWith0xef)

    let accounts' : AccountMap := -- (115)
      if deploymentFailed then checkpoint.accounts else
        let newAccount' := exec.accounts.findD address default
        exec.accounts.insert address { newAccount' with code := returnedData }

    { address := address
      createdAccounts := exec.createdAccounts
      accounts := accounts'
      gasRemaining := .ofNat <| if deploymentFailed then 0 else exec.gasAvailable.toNat - depositCost -- (114)
      substate := if deploymentFailed then checkpoint.substate else exec.substate -- (116)
      success := !deploymentFailed -- (117)
      output := .empty } -- (93)
  | .revert gasRemaining output =>
    { address := address
      createdAccounts := checkpoint.createdAccounts
      accounts := checkpoint.accounts
      gasRemaining := gasRemaining
      substate := checkpoint.substate
      success := false
      output := output }
  | .exception _ =>
    { address := address
      createdAccounts := checkpoint.createdAccounts
      accounts := checkpoint.accounts
      gasRemaining := 0
      substate := checkpoint.substate
      success := false
      output := .empty }

/--
Resume a frame suspended on CREATE/CREATE2: restore the unused gas (the
parent retained `g − L(g)`), set the return data on failure, push the new
contract's address (or 0), and advance the pc.
-/
def resumeAfterCreate (result : CreateResult) (pd : PendingCreate) :
    Except ExecutionException Frame := do
  let evmState := pd.frame.exec
  let gas := evmState.gasAvailable
  let gasRemaining := result.gasRemaining
  let success := result.success
  let pushedValue : UInt256 :=
    let balance := pd.callerAccounts.find? evmState.executionEnv.address |>.option 0 (·.balance)
    if success = false ∨ evmState.executionEnv.depth = 1024 ∨ pd.value > balance ∨ pd.initCodeSize > 49152
    then 0 else .ofNat result.address
  let newReturnData : ByteArray := if success then .empty else result.output
  if (gas + gasRemaining).toNat < allButOneSixtyFourth gas.toNat then
    throw .OutOfGas
  let exec' :=
    { evmState with
        accounts := result.accounts
        substate := result.substate
        createdAccounts := result.createdAccounts
        activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat pd.initOffset.toNat pd.initSize.toNat
        returnData := newReturnData
        gasAvailable := .ofNat <| gas.toNat - allButOneSixtyFourth gas.toNat + gasRemaining.toNat }
  return { pd.frame with exec := exec'.replaceStackAndIncrPC (pd.stack.push pushedValue) }

end Evm
