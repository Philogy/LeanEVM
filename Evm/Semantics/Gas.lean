import Mathlib.Data.Nat.Log

import Evm.State
import Evm.StateOps
import Evm.State.TransactionOps
import Evm.Semantics.GasConstants

namespace Evm

/-
Appendix G. Fee Schedule — the named gas formulas.

Every formula takes the operands it prices explicitly (already popped by the
instruction's dispatch arm); none of them peeks at machine state.
-/

section Gas

open GasConstants

/--
The memory cost function `Cₘ` (328).
-/
def Cₘ (a : UInt64) : ℕ :=
  let a : ℕ := a.toNat
  Gmemory * a + ((a * a) / QuadraticCeofficient)
  where QuadraticCeofficient : ℕ := 512

/-- `CSSTORE` (Appendix G / EIP-2200, sans the stipend check). -/
def sstoreCost (originalValue currentValue newValue : UInt256) (warm : Bool) : ℕ :=
  let loadComponent := if warm then 0 else Gcoldsload
  let storeComponent :=
    if currentValue = newValue || originalValue ≠ currentValue                          then Gwarmaccess else
    if currentValue ≠ newValue && originalValue = currentValue && originalValue = 0 then Gsset else
    /- currentValue ≠ newValue ∧ originalValue = currentValue ∧ originalValue ≠ 0 -/     Gsreset
  loadComponent + storeComponent

def tstoreCost : ℕ :=
  Gwarmaccess

/--
The warm/cold account-access cost (EIP-2929), used by BALANCE, EXTCODESIZE,
EXTCODECOPY, EXTCODEHASH and the CALL family.
-/
def accessCost (a : AccountAddress) (substate : Substate) : ℕ :=
  if substate.accessedAccounts.contains a
  then Gwarmaccess
  else Gcoldaccountaccess

/-- `CSELFDESTRUCT`: `warm` is the recipient's access status, `createsAccount`
the "dead recipient and nonzero self balance" condition. -/
def selfdestructCost (warm createsAccount : Bool) : ℕ :=
  Gselfdestruct + (if warm then 0 else Gcoldaccountaccess) + (if createsAccount then Gnewaccount else 0)

/-- `CSLOAD` (EIP-2929): `warm` is the storage key's access status. -/
def sloadCost (warm : Bool) : ℕ :=
  if warm then Gwarmaccess else Gcoldsload

def tloadCost : ℕ :=
  Gwarmaccess

/-- The EXP cost: `exponent` is `μs[1]`. -/
def expCost (exponent : UInt256) : ℕ :=
  if exponent == 0 then Gexp else Gexp + Gexpbyte * (1 + Nat.log 256 exponent.toNat)

/-- The KECCAK256 cost: `size` is the hashed range's byte length. -/
def keccakCost (size : UInt256) : ℕ :=
  Gkeccak256 + Gkeccak256word * ((size.toNat + 31) / 32)

/-- The per-word copy component of the *COPY instructions (`Gcopy ⌈size/32⌉`). -/
def copyCost (size : UInt256) : ℕ :=
  Gcopy * ((size.toNat + 31) / 32)

/-- The LOG0–LOG4 cost. -/
def logCost (topicCount : ℕ) (size : UInt256) : ℕ :=
  Glog + Glogdata * size.toNat + topicCount * Glogtopic

/--
(331)
-/
def allButOneSixtyFourth (n : ℕ) : ℕ := n - (n / 64)

def newAccountCost (t : AccountAddress) (val : UInt256) (accounts : AccountMap) : ℕ :=
  if Evm.State.dead accounts t && val != 0 then Gnewaccount else 0

def transferCost (val : UInt256) : ℕ :=
  if val != 0 then Gcallvalue else 0

def callExtraCost (t r : AccountAddress) (val : UInt256) (accounts : AccountMap) (substate : Substate) : ℕ :=
  accessCost t substate + transferCost val + newAccountCost r val accounts

/-- `CCALLGAS`'s cap: `gasAvailable` is the gas after the memory-expansion charge. -/
def callGasCap (t r : AccountAddress) (val g : UInt256) (accounts : AccountMap) (gasAvailable : UInt64) (substate : Substate) :=
  if gasAvailable.toNat >= callExtraCost t r val accounts substate then
    min (allButOneSixtyFourth <| (gasAvailable.toNat - callExtraCost t r val accounts substate)) g.toNat
  else
    g.toNat

/-- `CCALLGAS`: the child's gas allowance. -/
def callGas (t r : AccountAddress) (val g : UInt256) (accounts : AccountMap) (gasAvailable : UInt64) (substate : Substate) : ℕ :=
  match val with
    | 0 => callGasCap t r val g accounts gasAvailable substate
    | _ => callGasCap t r val g accounts gasAvailable substate + GasConstants.Gcallstipend

/-- `CCALL`: what the caller is charged. -/
def callCost (t r : AccountAddress) (val g : UInt256) (accounts : AccountMap) (gasAvailable : UInt64) (substate : Substate) : ℕ :=
  callGasCap t r val g accounts gasAvailable substate + callExtraCost t r val accounts substate

/--
(65)
-/
def initCodeCost (x : ℕ) : ℕ := Ginitcodeword * ((x + 31) / 32)

/-- `CCREATE`: `initSize` is `μs[2]`. -/
def createCost (initSize : UInt256) : ℕ :=
  Gcreate + initCodeCost initSize.toNat

/-- `CCREATE2`: CREATE plus hashing the init code. -/
def create2Cost (initSize : UInt256) : ℕ :=
  Gcreate + Gkeccak256word * ((initSize.toNat + 31) / 32) + initCodeCost initSize.toNat

def intrinsicGas (T : Transaction) : ℕ :=
  let dataCost :=
    T.base.data.foldl
      (λ acc b ↦
        acc +
          if b == 0 then
            GasConstants.Gtxdatazero
          else GasConstants.Gtxdatanonzero
      )
      0
  let createCost : ℕ :=
    if T.base.recipient == none then
      GasConstants.Gtxcreate + initCodeCost (T.base.data.size)
    else 0

  let accessListCost : ℕ :=
    T.getAccessList.foldl
      (λ acc (_, s) ↦
        acc + GasConstants.Gaccesslistaddress + s.size * GasConstants.Gaccessliststorage
      )
      0
  dataCost + createCost + GasConstants.Gtransaction + accessListCost

end Gas

end Evm
