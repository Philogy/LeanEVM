import Evm.State.SubstateOps
import Evm.State.AccountOps

import Evm.Maps.AccountMap

import Evm.State
import Evm.Wheels
import Evm.Semantics.GasConstants

namespace Evm

namespace State

def addAccessedAccount (self : State) (addr : AccountAddress) : State :=
  { self with substate := self.substate.addAccessedAccount addr }

def addAccessedStorageKey (self : State) (sk : AccountAddress × UInt256) : State :=
  { self with substate := self.substate.addAccessedStorageKey sk }

/--
DEAD(σ, a). Section 4.1., equation 15.
-/
def dead (σ : AccountMap) (addr : AccountAddress) : Bool :=
  σ.find? addr |>.option True Account.emptyAccount

def accountExists (self : State) (addr : AccountAddress) : Bool := self.accounts.find? addr |>.isSome

def lookupAccount (self : State) (addr : AccountAddress) : Option (Account) :=
  self.accounts.find? addr

def updateAccount (addr : AccountAddress) (act : Account) (self : State) : State :=
  { self with accounts := self.accounts.insert addr act }

def setAccount (self : State) (addr : AccountAddress) (acc : Account) : State :=
  { self with accounts := self.accounts.insert addr acc }

def updateAccount! (self : State) (addr : AccountAddress) (f : Account → Account) : State :=
  let acc! := self.lookupAccount addr |>.getD default
  self.setAccount addr (f acc!)

def balance (self : State) (k : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 k
  (self.addAccessedAccount addr, self.accounts.find? addr |>.elim 0 (·.balance))

def initialiseAccount (addr : AccountAddress) (self : State) : State :=
  if self.accountExists addr then self else self.updateAccount addr default

def calldataload (self : State) (v : UInt256) : UInt256 :=
  uInt256OfByteArray <| self.executionEnv.calldata.readBytes v.toNat 32

def setNonce! (self : State) (addr : AccountAddress) (nonce : UInt256) : State :=
  self.updateAccount! addr (λ acc ↦ { acc with nonce := nonce })

section CodeCopy

def extCodeSize (self : State) (a : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 a
  let s := self.lookupAccount addr |>.option 0 (.ofNat ∘ ByteArray.size ∘ (·.code))
  (self.addAccessedAccount addr, s)

def extCodeHash (self : State) (v : UInt256) : State × UInt256 :=
  let addr := AccountAddress.ofUInt256 v
  let newState := self.addAccessedAccount addr
  if dead self.accounts addr then (newState, 0) else
  let r := self.lookupAccount (AccountAddress.ofUInt256 v) |>.option 0 Account.codeHash
  (newState, r)

end CodeCopy

section Blocks

def blockHash (self : State) (blockNumber : UInt256) : UInt256 :=
  let v := self.executionEnv.blockHeader.number
  if v ≤ blockNumber.toNat || blockNumber.toNat + 256 < v then 0
  else
    let hashes := self.blockHashes
    hashes.getD blockNumber.toNat 0

def coinBase (self : State) : AccountAddress :=
  self.executionEnv.blockHeader.beneficiary

def timeStamp (self : State) : UInt256 :=
  .ofNat self.executionEnv.blockHeader.timestamp

def number (self : State) : UInt256 :=
  .ofNat self.executionEnv.blockHeader.number

def difficulty (self : State) : UInt256 :=
  .ofNat self.executionEnv.blockHeader.difficulty

def gasLimit (self : State) : UInt256 :=
  .ofNat self.executionEnv.blockHeader.gasLimit

def chainId (_ : State) : UInt256 := .ofNat Evm.chainId

def selfbalance (self : State) : UInt256 :=
  Batteries.RBMap.find? self.accounts self.executionEnv.address |>.elim 0 (·.balance)

end Blocks

section Storage

def setStorage! (self : State) (addr : AccountAddress) (strg : Storage) : State :=
  self.updateAccount! addr (λ acc ↦ { acc with storage := strg })

def sload (self : State) (spos : UInt256) : State × UInt256 :=
  let Iₐ := self.executionEnv.address
  let v := self.lookupAccount Iₐ |>.option 0 (Account.lookupStorage (k := spos))
  let state' := self.addAccessedStorageKey (Iₐ, spos)
  (state', v)

def sstore (self : State) (spos sval : UInt256) : State :=
  let Iₐ := self.executionEnv.address
  let { storage := σ_Iₐ, .. } := self.accounts.find! Iₐ
  let v₀ :=
    match self.originalAccounts.find? Iₐ with
      | none => 0
      | some acc => acc.storage.findD spos 0
  let v := σ_Iₐ.findD spos 0
  let v' := sval

  let r_dirtyclear : ℤ :=
    if v₀ ≠ .ofNat 0 && v = .ofNat 0 then - GasConstants.Rsclear else
    if v₀ ≠ .ofNat 0 && v' = .ofNat 0 then GasConstants.Rsclear else
    0

  let r_dirtyreset : ℤ :=
    if v₀ = v' && v₀ = .ofNat 0 then GasConstants.Gsset - GasConstants.Gwarmaccess else
    if v₀ = v' && v₀ ≠ .ofNat 0 then GasConstants.Gsreset - GasConstants.Gwarmaccess else
    0

  let ΔAᵣ : ℤ :=
    if v ≠ v' && v₀ = v && v' = .ofNat 0 then GasConstants.Rsclear else
    if v ≠ v' && v₀ ≠ v then r_dirtyclear + r_dirtyreset else
    0

  let newAᵣ : UInt256 :=
    match ΔAᵣ with
      | .ofNat n => self.substate.refundBalance + .ofNat n
      | .negSucc n => self.substate.refundBalance - .ofNat n - 1
  self.lookupAccount Iₐ |>.option self λ acc ↦
    let self' :=
      self.setAccount Iₐ (acc.updateStorage spos sval)
        |>.addAccessedStorageKey (Iₐ, spos)
    { self' with substate.refundBalance := newAᵣ }

def tload (self : State) (spos : UInt256) : State × UInt256 :=
  let Iₐ := self.executionEnv.address
  let v := self.lookupAccount Iₐ |>.option 0 (Account.lookupTransientStorage (k := spos))
  (self, v)

def tstore (self : State) (spos sval : UInt256) : State :=
  let Iₐ := self.executionEnv.address
  self.lookupAccount Iₐ |>.option self λ acc ↦
    self.updateAccount Iₐ (acc.updateTransientStorage spos sval)

end Storage

end State

end Evm
