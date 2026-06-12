import Evm.Semantics.Call
import Evm.Semantics.Create
import Evm.Semantics.Frame
import Evm.Semantics.Step

namespace Evm

/-- Package a frame's halt into its result via the frame-kind's `end` function. -/
def endFrame (fr : Frame) (halt : FrameHalt) : FrameResult :=
  match fr.kind with
    | .call checkpoint => .call (endCall checkpoint halt)
    | .create address checkpoint => .create (endCreate address checkpoint halt)

/-- Resume a suspended parent frame with its child's result. -/
def Pending.resume (p : Pending) (result : FrameResult) : Except ExecutionException Frame :=
  match p with
    | .call pd => .ok (resumeAfterCall result.toCallResult pd)
    | .create pd => resumeAfterCreate result.toCreateResult pd

/-- The suspended parent frame of a pending call/create. -/
def Pending.frame : Pending → Frame
  | .call pd => pd.frame
  | .create pd => pd.frame

/--
The interpreter driver — the only recursion in the EVM semantics.

The machine is either executing the `current` frame (`.inl`) or delivering a
finished child's result to the innermost suspended frame (`.inr`); `stack`
holds the suspended ancestors. One iteration is one instruction, one
call/create descent, or one result delivery.

`fuel` is an implementation detail, not a semantic bound: it is seeded from
the gas limit (see `seedFuel`) and cannot run out for gas-respecting
executions, because every non-halting instruction costs at least 1 gas and
each descent/delivery pair is matched to a call charge of at least 100 gas.
`.OutOfFuel` therefore signals a broken gas table, not a program behavior.
-/
def drive (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult) :
    Except ExecutionException FrameResult :=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 =>
      match state with
        | .inr result =>
          match stack with
            | [] => .ok result
            | pending :: rest =>
              match pending.resume result with
                | .ok parent => drive fuel rest (.inl parent)
                | .error e =>
                  -- The resume itself faulted: the parent frame halts
                  -- exceptionally and its own result propagates up.
                  drive fuel rest (.inr (endFrame pending.frame (.exception e)))
        | .inl current =>
          match stepFrame current with
            | .next exec => drive fuel stack (.inl { current with exec := exec })
            | .halt halt => drive fuel stack (.inr (endFrame current halt))
            | .needsCall params pending =>
              match beginCall params with
                | .inl child => drive fuel (.call pending :: stack) (.inl child)
                | .inr result => drive fuel (.call pending :: stack) (.inr (.call result))
            | .needsCreate params pending =>
              match beginCreate params with
                | .ok child => drive fuel (.create pending :: stack) (.inl child)
                | .error _ =>
                  -- Mirrors the historical behavior of a faulting `Λ`: the
                  -- CREATE instruction completes with a zeroed result and an
                  -- emptied account map.
                  let exec := pending.frame.exec
                  let result : CreateResult :=
                    { address := 0
                      createdAccounts := exec.createdAccounts
                      accounts := ∅
                      gasRemaining := 0
                      substate := exec.substate
                      success := false
                      output := .empty }
                  drive fuel (.create pending :: stack) (.inr (.create result))

/--
The driver's step budget for a top-level execution with gas limit `gas` —
generous (see `drive`): instructions cost ≥ 1 gas each and descents ≥ 100, so
`2 * gas` already overshoots; the constant covers the zero-gas edge cases.
-/
def seedFuel (gas : UInt256) : ℕ := 2 * gas.toNat + 4096

/--
Message call — the YP's `Θ` (eq. 119): execute `params.codeSource` in the
context described by `params`, returning the final world state, remaining
gas, and output.
-/
def messageCall (params : CallParams) : Except ExecutionException CallResult :=
  match beginCall params with
    | .inr result => .ok result
    | .inl frame => FrameResult.toCallResult <$> drive (seedFuel params.gas) [] (.inl frame)

/--
Contract creation — the YP's `Λ` (eq. 93): derive the new address, run the
init code, and deposit the returned code.
-/
def createContract (params : CreateParams) : Except ExecutionException CreateResult := do
  let frame ← beginCreate params
  FrameResult.toCreateResult <$> drive (seedFuel params.gas) [] (.inl frame)

end Evm
