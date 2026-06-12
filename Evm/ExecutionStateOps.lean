import Mathlib.Data.List.Intervals

import Evm.UInt256
import Evm.ExecutionState
import Evm.State.AccountOps
import Evm.StateOps

namespace Evm



namespace ExecutionState

section Instructions

def incrPC (I : ExecutionState) (pcΔ : ℕ := 1) : ExecutionState :=
  { I with pc := I.pc + .ofNat pcΔ }

def replaceStackAndIncrPC (I : ExecutionState) (s : Stack UInt256) (pcΔ : ℕ := 1) : ExecutionState :=
  { I with stack := s, pc := I.pc + .ofNat pcΔ }

end Instructions

def liftMState {m} [Monad m] (f : Evm.State → m (Evm.State)) : ExecutionState → m ExecutionState :=
  λ s ↦ do pure { s with toState := ← f s.toState }

instance {m} [Monad m] : CoeFun (Evm.State → m (Evm.State)) (λ _ ↦ ExecutionState → m ExecutionState) := ⟨liftMState⟩

def liftState (f : Evm.State → Evm.State) : ExecutionState → ExecutionState :=
  liftMState (m := Id) f

instance : CoeFun (Evm.State → Evm.State) (λ _ ↦ ExecutionState → ExecutionState) := ⟨liftState⟩

def initialiseAccount (addr : AccountAddress) : ExecutionState → ExecutionState :=
  Evm.State.initialiseAccount addr

def updateAccount (addr : AccountAddress) (act : Account) : ExecutionState → ExecutionState :=
  Evm.State.updateAccount addr act

def isEmpty (self : ExecutionState) : Bool := self.toState.accountMap == ∅

end ExecutionState



end Evm
