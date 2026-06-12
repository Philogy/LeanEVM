import Evm.Exception
import Evm.Machine.Stack
import Evm.Machine.ExecutionState
import Evm.Machine.ExecutionStateOps
import Evm.Machine.MachineStateOps
import Evm.Machine.SharedStateOps
import Evm.Semantics.Frame
import Evm.Semantics.Gas
import Evm.Semantics.GasConstants
import Evm.State
import Evm.StateOps

/-!
The building blocks of the instruction dispatcher (`Evm.Semantics.Dispatch`):
gas-charging helpers and the higher-order wrappers shared by the simple
instruction arms. Every wrapper charges its (defaulted) cost itself, with the
already-popped operands in hand.
-/

namespace Evm

open GasConstants

/-- The result of one instruction arm: a `Signal` or an exceptional halt. -/
abbrev Step := Except ExecutionException Signal

instance : MonadLift Option (Except ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

/-- The frame continues executing with the updated state. -/
@[inline] def continueWith (exec : ExecutionState) : Step := .ok (.next exec)

/-- Check-and-subtract a gas cost: `OutOfGass` when unaffordable. -/
@[inline] def charge (cost : ℕ) (exec : ExecutionState) :
    Except ExecutionException ExecutionState :=
  if exec.gasAvailable.toNat < cost then .error .OutOfGass
  else .ok { exec with gasAvailable := exec.gasAvailable - .ofNat cost }

/--
Charge the memory-expansion component of H.1 — `Cₘ(μᵢ′) − Cₘ(μᵢ)` with
`μᵢ′ = M(μᵢ, offset, size)`. Only the cost is charged here; `activeWords`
itself is updated by the instruction's own semantics.
-/
@[inline] def chargeMemExpansion (exec : ExecutionState) (offset size : ℕ) :
    Except ExecutionException ExecutionState :=
  let words' : UInt256 := .ofNat <| MachineState.M exec.activeWords.toNat offset size
  charge (Cₘ words' - Cₘ exec.activeWords) exec

/-- `StaticModeViolation` unless the frame may modify state (the YP's `W` set, eq. 159). -/
@[inline] def requireStateMod (exec : ExecutionState) : Except ExecutionException Unit :=
  if exec.executionEnv.canModifyState then .ok () else .error .StaticModeViolation

/-- Pop one word, push `f` of it. -/
def unOp (f : UInt256 → UInt256) (exec : ExecutionState) (cost : ℕ := Gverylow) : Step := do
  let exec ← charge cost exec
  let (stack, a) ← exec.stack.pop
  continueWith <| exec.replaceStackAndIncrPC (stack.push (f a))

/-- Pop two words, push `f` of them. -/
def binOp (f : UInt256 → UInt256 → UInt256) (exec : ExecutionState) (cost : ℕ := Gverylow) : Step := do
  let exec ← charge cost exec
  let (stack, a, b) ← exec.stack.pop2
  continueWith <| exec.replaceStackAndIncrPC (stack.push (f a b))

/-- Pop three words, push `f` of them. -/
def ternOp (f : UInt256 → UInt256 → UInt256 → UInt256) (exec : ExecutionState) (cost : ℕ := Gverylow) : Step := do
  let exec ← charge cost exec
  let (stack, a, b, c) ← exec.stack.pop3
  continueWith <| exec.replaceStackAndIncrPC (stack.push (f a b c))

/-- Push a value read from the execution state (environment/machine/world readers). -/
def pushOp (v : ExecutionState → UInt256) (exec : ExecutionState) (cost : ℕ := Gbase) : Step := do
  let exec ← charge cost exec
  continueWith <| exec.replaceStackAndIncrPC (exec.stack.push (v exec))

/--
Pop one word, apply a world-state operation returning the new state and the
pushed value; the cost may depend on the popped operand (warm/cold access).
-/
def unStateOp (f : Evm.State → UInt256 → Evm.State × UInt256)
    (cost : ExecutionState → UInt256 → ℕ) (exec : ExecutionState) : Step := do
  let (stack, a) ← exec.stack.pop
  let exec ← charge (cost exec a) exec
  let (state', v) := f exec.toState a
  continueWith <| ExecutionState.replaceStackAndIncrPC { exec with toState := state' } (stack.push v)

/-- DUPn (`n ∈ [1, 16]`). -/
def dup (n : ℕ) (exec : ExecutionState) : Step := do
  let exec ← charge Gverylow exec
  let some v := exec.stack[n-1]? | throw .StackUnderflow
  continueWith <| exec.replaceStackAndIncrPC (v :: exec.stack)

/-- SWAPn (`n ∈ [1, 16]`). -/
def swap (n : ℕ) (exec : ExecutionState) : Step := do
  let exec ← charge Gverylow exec
  let top := exec.stack.take (n + 1)
  let bottom := exec.stack.drop (n + 1)
  if List.length top = (n + 1) then
    continueWith <| exec.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    throw .StackUnderflow

/-- LOG0–LOG4 tail: operands already popped, `topics` collected by the arm. -/
def logArm (exec : ExecutionState) (stack : Stack UInt256) (offset size : UInt256)
    (topics : Array UInt256) : Step := do
  requireStateMod exec
  let exec ← chargeMemExpansion exec offset.toNat size.toNat
  let exec ← charge (logCost topics.size size) exec
  let shared' := SharedState.logOp offset size topics exec.toSharedState
  continueWith <| ExecutionState.replaceStackAndIncrPC { exec with toSharedState := shared' } stack

end Evm
