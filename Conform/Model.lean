import Lean.Data.RBMap
import Lean.Data.Json

-- import EvmYul.Maps
import EvmYul.Operations
import EvmYul.Wheels
import EvmYul.State.Withdrawal
import EvmYul.State.Block

import EvmYul.EVM.State

import Conform.Wheels

namespace EvmYul

namespace Conform

section Model

open Lean

def AddrMap.keys {α : Type} [Inhabited α] (self : AddrMap α) : Multiset AccountAddress :=
  .ofList <| self.toList.map Prod.fst

private abbrev sigmaLe (lhs rhs : (_ : UInt256) × UInt256) : Prop :=
  if lhs.1.toNat = rhs.1.toNat then lhs.2.toNat ≤ rhs.2.toNat else lhs.1.toNat ≤ rhs.1.toNat

instance : LE ((_ : UInt256) × UInt256) := ⟨sigmaLe⟩

instance : DecidableRel (α := (_ : UInt256) × UInt256) (· ≤ ·) :=
  λ a b ↦ inferInstanceAs (Decidable (sigmaLe a b))

instance : IsTrans ((_ : UInt256) × UInt256) (· ≤ ·) where
  trans a b c h₁ h₂ := by
    simp only [LE.le, sigmaLe] at *
    grind

instance : IsAntisymm ((_ : UInt256) × UInt256) (· ≤ ·) where
  antisymm a b h₁ h₂ := by
    obtain ⟨a₁, a₂⟩ := a
    obtain ⟨b₁, b₂⟩ := b
    simp only [LE.le, sigmaLe] at h₁ h₂
    grind [EvmYul.UInt256.toNat_inj]

instance : IsTotal ((_ : UInt256) × UInt256) (· ≤ ·) where
  total a b := by
    simp only [LE.le, sigmaLe]
    grind

abbrev Code := ByteArray

abbrev Pre := PersistentAccountMap

abbrev PostEntry := PersistentAccountState

abbrev Post := PersistentAccountMap

abbrev Transactions := Array Transaction

abbrev Withdrawals := Array Withdrawal

private local instance : Repr Json := ⟨λ s _ ↦ Json.pretty s⟩

/--
In theory, parts of the TestEntry could deserialise immediately into the underlying `EVM.State`.
-/

inductive PostState where
  | Hash : ByteArray → PostState
  | Map : Post → PostState
  deriving Inhabited

structure TestEntry where
  info               : Json := ""
  blocks             : RawBlocks
  genesisRLP         : ByteArray
  lastblockhash      : UInt256
  network            : String
  postState          : PostState
  pre                : Pre
  sealEngine         : Json := ""
  deriving Inhabited

abbrev TestMap := Batteries.RBMap String TestEntry compare

abbrev AccessListEntry := AccountAddress × Array UInt256

abbrev AccessList := Array AccessListEntry

def TestResult := Option String
  deriving Repr, Inhabited

namespace TestResult

def isSuccess (self : TestResult) : Bool := self matches none

def isFailure (self : TestResult) : Bool := !self.isSuccess

def mkFailed (reason : String := "") : TestResult := .some reason

def mkSuccess : TestResult := .none

def ofBool (success : Bool) (reason : String := "Semantics error.") : TestResult :=
  if success then mkSuccess else mkFailed reason

end TestResult

end Model
