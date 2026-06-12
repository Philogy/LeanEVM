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

/-- The address-derivation preimage `contractAddressBytes` (eq. 96). -/
private def contractAddressBytes (s : AccountAddress) (n : UInt256) (ζ : Option ByteArray) (i : ByteArray) :
  Option ByteArray
:=
  let s := s.toByteArray
  let n := BE n.toNat
  match ζ with
    | none   => Rlp.encode <| .list [.bytes s, .bytes n]
    | some ζ => .some <| BE 255 ++ s ++ ζ ++ ffi.KEC i

/--
Enter a contract creation — the YP's `Λ` (eq. 93) up to the recursive code
execution: address derivation (eq. 94–96), the EIP-7610 occupied-address
check, account initialisation (eq. 97–99), and execution-environment
construction.
-/
def beginCreate (params : CreateParams) : Except ExecutionException Frame := do
  let σ := params.accounts
  let s := params.caller

  -- EIP-3860 (includes EIP-170)
  -- https://eips.ethereum.org/EIPS/eip-3860

  let n : UInt256 := (σ.find? s |>.option 0 (·.nonce)) - 1
  let some lₐ := contractAddressBytes s n params.salt params.initCode | .error .StackUnderflow
  let a : AccountAddress := -- (94) (95)
    (ffi.KEC lₐ).extract 12 32 /- 160 bits = 20 bytes -/
      |> fromByteArrayBigEndian |> Fin.ofNat _

  -- A* (97)
  let AStar := params.substate.addAccessedAccount a
  -- σ*
  let existentAccount := σ.findD a default

  /-
    https://eips.ethereum.org/EIPS/eip-7610
    If a contract creation is attempted due to a creation transaction,
    the CREATE opcode, the CREATE2 opcode, or any other reason,
    and the destination address already has either a nonzero nonce,
    a nonzero code length, or non-empty storage, then the creation MUST throw
    as if the first byte in the init code were an invalid opcode.
  -/
  let (i, createdAccounts) :=
    if
      existentAccount.nonce ≠ 0
        || existentAccount.code.size ≠ 0
        || existentAccount.storage != default
    then
      (⟨#[0xfe]⟩, params.createdAccounts)
    else (params.initCode, params.createdAccounts.insert a)

  let newAccount : Account :=
    { existentAccount with
        nonce := existentAccount.nonce + 1
        balance := params.value + existentAccount.balance
    }

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σStar :=
    match σ.find? s with
      | none => σ
      | some ac =>
        σ.insert s { ac with balance := ac.balance - params.value }
          |>.insert a newAccount -- (99)
  -- I
  let exEnv : ExecutionEnv :=
    { address := a
    , origin    := params.origin
    , caller    := s
    , value  := params.value
    , calldata  := default
    , code      := i
    , gasPrice  := params.gasPrice.toNat
    , blockHeader := params.blockHeader
    , depth     := params.depth
    , canModifyState      := params.canModifyState
    , blobVersionedHashes := params.blobVersionedHashes
    }
  .ok
    { kind := .create a ⟨createdAccounts, σ, AStar⟩
      validJumps := validJumpDests i 0
      exec :=
        { (default : ExecutionState) with
            accounts := σStar
            originalAccounts := params.originalAccounts
            executionEnv := exEnv
            substate := AStar
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
    let c := GasConstants.Gcodedeposit * returnedData.size

    let F : Bool := Id.run do -- (118)
      let F₀ : Bool :=
        match checkpoint.accounts.find? address with
        | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ 0
        | .none => false
      let F₂ : Bool := exec.gasAvailable.toNat < c
      let MAX_CODE_SIZE := 24576
      let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
      let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
      pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)

    let σ' : AccountMap := -- (115)
      if F then checkpoint.accounts else
        let newAccount' := exec.accounts.findD address default
        exec.accounts.insert address { newAccount' with code := returnedData }

    { address := address
      createdAccounts := exec.createdAccounts
      accounts := σ'
      gasRemaining := .ofNat <| if F then 0 else exec.gasAvailable.toNat - c -- (114)
      substate := if F then checkpoint.substate else exec.substate -- (116)
      success := !F -- (117)
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
parent retained `g − allButOneSixtyFourth(g)`), set the return data on failure, push the new
contract's address (or 0), and advance the pc.
-/
def resumeAfterCreate (result : CreateResult) (pd : PendingCreate) :
    Except ExecutionException Frame := do
  let evmState := pd.frame.exec
  let g := evmState.gasAvailable
  let g' := result.gasRemaining
  let z := result.success
  let x : UInt256 :=
    let balance := pd.callerAccounts.find? evmState.executionEnv.address |>.option 0 (·.balance)
    if z = false ∨ evmState.executionEnv.depth = 1024 ∨ pd.value > balance ∨ pd.initCodeSize > 49152
    then 0 else .ofNat result.address
  let newReturnData : ByteArray := if z then .empty else result.output
  if (g + g').toNat < allButOneSixtyFourth g.toNat then
    throw .OutOfGass
  let exec' :=
    { evmState with
        accounts := result.accounts
        substate := result.substate
        createdAccounts := result.createdAccounts
        activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat pd.initOffset.toNat pd.initSize.toNat
        returnData := newReturnData
        gasAvailable := .ofNat <| g.toNat - allButOneSixtyFourth g.toNat + g'.toNat }
  return { pd.frame with exec := exec'.replaceStackAndIncrPC (pd.stack.push x) }

end Evm
