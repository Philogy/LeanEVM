import Evm.Gas
import Evm.Semantics.Call
import Evm.Semantics.Create
import Evm.Semantics.Decode
import Evm.Semantics.Frame
import Evm.Semantics.Interpreter
import Evm.Semantics.Params
import Evm.Semantics.Step
import Evm.State.TransactionOps
import Evm.StateOps

namespace Evm

open Batteries (RBMap RBSet)

-- Type Υ using \Upsilon or \GU
def Υ
  (σ : AccountMap)
  (H_f : ℕ)
  (H : BlockHeader)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (T : Transaction)
  (S_T : AccountAddress)
  : Except Exception TransactionResult
:= do
  let g₀ : ℕ := intrinsicGas T
  -- "here can be no invalid transactions from this point"
  let senderAccount := (σ.find? S_T).get!
  -- The priority fee (67)
  let f :=
    match T with
      | .legacy t | .access t =>
            t.gasPrice - .ofNat H_f
      | .dynamic t | .blob t =>
            min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)
  -- The effective gas price
  let p := -- (66)
    match T with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ => f + .ofNat H_f
  let senderAccount :=
    { senderAccount with
        /-
          https://eips.ethereum.org/EIPS/eip-4844
          "The actual blob_fee as calculated via calc_blob_fee is deducted from
          the sender balance before transaction execution and burned, and is not
          refunded in case of transaction failure."
        -/
        balance := senderAccount.balance - T.base.gasLimit * p - .ofNat (calcBlobFee H T)  -- (74)
        nonce := senderAccount.nonce + 1 -- (75)
    }
  -- The checkpoint state (73)
  let σ₀ := σ.insert S_T senderAccount
  let accessList := T.getAccessList
  let AStar_K : List (AccountAddress × UInt256) := do -- (78)
    let ⟨Eₐ, Eₛ⟩ ← accessList
    let eₛ ← Eₛ.toList
    pure (Eₐ, eₛ)
  let a := -- (80)
    A0.accessedAccounts.insert S_T
      |>.insert H.beneficiary
      |>.union <| Batteries.RBSet.ofList (accessList.map Prod.fst) compare
  -- (81)
  let g := .ofNat <| T.base.gasLimit.toNat - g₀
  let AStarₐ := -- (79)
    match T.base.recipient with
      | some t => a.insert t
      | none => a
  let AStar := -- (77)
    { A0 with accessedAccounts := AStarₐ, accessedStorageKeys := Batteries.RBSet.ofList AStar_K Substate.storageKeysCmp}
  let (/- provisional state -/ σ_P, g', A, z) ← -- (76)
    match T.base.recipient with
      | none => do
        match
          createContract
            { blobVersionedHashes := T.blobVersionedHashes
              createdAccounts := .empty
              genesisBlockHeader := genesisBlockHeader
              blocks := blocks
              accounts := σ₀
              originalAccounts := σ₀
              substate := AStar
              caller := S_T
              origin := S_T
              gas := g
              gasPrice := p
              value := T.base.value
              initCode := T.base.data
              depth := 0
              salt := none
              blockHeader := H
              canModifyState := true }
        with
          | .ok r => pure (r.accounts, r.gasRemaining, r.substate, r.success)
          | .error e => .error <| .ExecutionException e
      | some t =>
        -- Proposition (71) suggests the recipient can be inexistent
        match
          messageCall
            { blobVersionedHashes := T.blobVersionedHashes
              createdAccounts := .empty
              genesisBlockHeader := genesisBlockHeader
              blocks := blocks
              accounts := σ₀
              originalAccounts := σ₀
              substate := AStar
              caller := S_T
              origin := S_T
              recipient := t
              codeSource := toExecute σ₀ t
              gas := g
              gasPrice := p
              value := T.base.value
              apparentValue := T.base.value
              calldata := T.base.data
              depth := 0
              blockHeader := H
              canModifyState := true }
        with
          | .ok r => pure (r.accounts, r.gasRemaining, r.substate, r.success)
          | .error e => .error <| .ExecutionException e
  -- The amount to be refunded (82)
  let gStar := g' + min ((T.base.gasLimit - g') / 5) A.refundBalance
  -- The pre-final state (83)
  let σStar :=
    σ_P.increaseBalance S_T (gStar * p)

  let beneficiaryFee := (T.base.gasLimit - gStar) * f
  let σStar' :=
    if beneficiaryFee != 0 then
      σStar.increaseBalance H.beneficiary beneficiaryFee
    else σStar
  let σ' := A.selfDestructSet.1.foldl Batteries.RBMap.erase σStar' -- (87)
  let deadAccounts := A.touchedAccounts.filter (Evm.State.dead σStar' ·)
  let σ' := deadAccounts.foldl Batteries.RBMap.erase σ' -- (88)
  let σ' := σ'.map λ (addr, acc) ↦ (addr, { acc with tstorage := .empty})
  .ok { accounts := σ', substate := A, success := z, gasUsed := T.base.gasLimit - gStar }

end Evm
