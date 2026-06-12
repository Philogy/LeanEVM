import Evm.Semantics.Gas
import Evm.Semantics.Call
import Evm.Semantics.Create
import Evm.Semantics.Decode
import Evm.Semantics.Frame
import Evm.Semantics.Interpreter
import Evm.Semantics.Params
import Evm.Semantics.Halt
import Evm.Semantics.Smsf
import Evm.Semantics.System
import Evm.Semantics.Dispatch
import Evm.State.TransactionOps
import Evm.StateOps

namespace Evm

open Batteries (RBMap RBSet)

/-- Execute one transaction — the YP's `Υ` (section 6). -/
def executeTransaction
  (chainId : UInt256)
  (accounts : AccountMap)
  (baseFee : ℕ)
  (header : BlockHeader)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (tx : Transaction)
  (sender : AccountAddress)
  : Except Exception TransactionResult
:= do
  let intrinsicCost : ℕ := intrinsicGas tx
  -- "here can be no invalid transactions from this point"
  let senderAccount := (accounts.find? sender).get!
  -- The priority fee (67)
  let priorityFee :=
    match tx with
      | .legacy t | .access t =>
            t.gasPrice - .ofNat baseFee
      | .dynamic t | .blob t =>
            min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat baseFee)
  -- The effective gas price
  let effectiveGasPrice := -- (66)
    match tx with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ => priorityFee + .ofNat baseFee
  let senderAccount :=
    { senderAccount with
        /-
          https://eips.ethereum.org/EIPS/eip-4844
          "The actual blob_fee as calculated via calc_blob_fee is deducted from
          the sender balance before transaction execution and burned, and is not
          refunded in case of transaction failure."
        -/
        balance := senderAccount.balance - tx.base.gasLimit * effectiveGasPrice - .ofNat (calcBlobFee header tx)  -- (74)
        nonce := senderAccount.nonce + 1 -- (75)
    }
  -- The checkpoint state (73)
  let checkpointState := accounts.insert sender senderAccount
  let accessList := tx.getAccessList
  let accessedStorageKeys : List (AccountAddress × UInt256) := do -- (78)
    let ⟨entryAddress, entryKeys⟩ ← accessList
    let entryKey ← entryKeys.toList
    pure (entryAddress, entryKey)
  let baseAccessedAccounts := -- (80)
    initialSubstate.accessedAccounts.insert sender
      |>.insert header.beneficiary
      |>.union <| Batteries.RBSet.ofList (accessList.map Prod.fst) compare
  -- (81)
  let gas := .ofNat <| tx.base.gasLimit.toNat - intrinsicCost
  let accessedAccounts := -- (79)
    match tx.base.recipient with
      | some t => baseAccessedAccounts.insert t
      | none => baseAccessedAccounts
  let substate₀ := -- (77)
    { initialSubstate with accessedAccounts := accessedAccounts, accessedStorageKeys := Batteries.RBSet.ofList accessedStorageKeys Substate.storageKeysCmp}
  let (/- provisional state -/ provisionalState, gasRemaining, substate, success) ← -- (76)
    match tx.base.recipient with
      | none => do
        match
          createContract
            { blobVersionedHashes := tx.blobVersionedHashes
              createdAccounts := .empty
              genesisBlockHeader := genesisBlockHeader
              blocks := blocks
              accounts := checkpointState
              originalAccounts := checkpointState
              substate := substate₀
              caller := sender
              origin := sender
              gas := gas
              gasPrice := effectiveGasPrice
              value := tx.base.value
              initCode := tx.base.data
              depth := 0
              salt := none
              blockHeader := header
              chainId := chainId
              canModifyState := true }
        with
          | .ok r => pure (r.accounts, r.gasRemaining, r.substate, r.success)
          | .error e => .error <| .ExecutionException e
      | some t =>
        -- Proposition (71) suggests the recipient can be inexistent
        match
          messageCall
            { blobVersionedHashes := tx.blobVersionedHashes
              createdAccounts := .empty
              genesisBlockHeader := genesisBlockHeader
              blocks := blocks
              accounts := checkpointState
              originalAccounts := checkpointState
              substate := substate₀
              caller := sender
              origin := sender
              recipient := t
              codeSource := toExecute checkpointState t
              gas := gas
              gasPrice := effectiveGasPrice
              value := tx.base.value
              apparentValue := tx.base.value
              calldata := tx.base.data
              depth := 0
              blockHeader := header
              chainId := chainId
              canModifyState := true }
        with
          | .ok r => pure (r.accounts, r.gasRemaining, r.substate, r.success)
          | .error e => .error <| .ExecutionException e
  -- The amount to be refunded (82)
  let gasRefunded := gasRemaining + min ((tx.base.gasLimit - gasRemaining) / 5) substate.refundBalance
  -- The pre-final state (83)
  let accountsWithRefund :=
    provisionalState.increaseBalance sender (gasRefunded * effectiveGasPrice)

  let beneficiaryFee := (tx.base.gasLimit - gasRefunded) * priorityFee
  let accountsWithFees :=
    if beneficiaryFee != 0 then
      accountsWithRefund.increaseBalance header.beneficiary beneficiaryFee
    else accountsWithRefund
  let accounts' := substate.selfDestructSet.1.foldl Batteries.RBMap.erase accountsWithFees -- (87)
  let deadAccounts := substate.touchedAccounts.filter (Evm.State.dead accountsWithFees ·)
  let accounts' := deadAccounts.foldl Batteries.RBMap.erase accounts' -- (88)
  let accounts' := accounts'.map λ (addr, acc) ↦ (addr, { acc with tstorage := .empty})
  .ok { accounts := accounts', substate := substate, success := success, gasUsed := tx.base.gasLimit - gasRefunded }

end Evm
