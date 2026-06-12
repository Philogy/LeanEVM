import Evm.UInt256
import Evm.Machine.ExecutionState
import Evm.Semantics.Params

namespace Evm

/--
The revert target of a running frame: the world state captured when the frame
was entered. On exceptional halt (and partially on revert / failed code
deposit) the frame's result is rebuilt from this snapshot. The maps are
persistent, so a checkpoint is a set of shared references, not a copy.
-/
structure Checkpoint where
  createdAccounts : Batteries.RBSet AccountAddress compare
  accounts        : AccountMap
  substate        : Substate

/--
What kind of execution a frame is, plus the data its `endCall`/`endCreate`
needs once it halts.
-/
inductive FrameKind where
  | call   (checkpoint : Checkpoint)
  | create (address : AccountAddress) (checkpoint : Checkpoint)

/--
A running code-execution frame: one activation of the interpreter loop.
`validJumps` is the frame's JUMPDEST analysis (the YP's `D(c)`), computed
once on frame entry.
-/
structure Frame where
  kind       : FrameKind
  validJumps : Array UInt32
  exec       : ExecutionState

def Frame.get_dest (f : Frame) (dest : UInt256) : Option UInt32 :=
  f.validJumps.find? (fun actual => UInt256.ofUInt32 actual = dest)

/-- How a frame finished executing. -/
inductive FrameHalt where
  /-- Normal halt (STOP/RETURN/SELFDESTRUCT): final state and output data. -/
  | success (exec : ExecutionState) (output : ByteArray)
  /-- REVERT: remaining gas and revert data; state rolls back to the checkpoint. -/
  | revert (gasRemaining : UInt256) (output : ByteArray)
  /-- Exceptional halt: all gas is consumed, state rolls back to the checkpoint. -/
  | exception (e : ExecutionException)

/-- The finished frame's result, tagged with the kind of frame it came from. -/
inductive FrameResult where
  | call   (result : CallResult)
  | create (result : CreateResult)

/--
A parent frame suspended on a CALL-family instruction: everything needed to
resume it once the child call's result is known. `stack` is the operand stack
with the instruction's arguments already popped (the success flag is pushed
onto it); `callerAccounts` is the account map from before the call, used by
the YP's `x` success-flag re-checks.
-/
structure PendingCall where
  frame          : Frame
  stack          : Stack UInt256
  callerAccounts : AccountMap
  value          : UInt256
  inOffset       : UInt256
  inSize         : UInt256
  outOffset      : UInt256
  outSize        : UInt256

/--
A parent frame suspended on CREATE/CREATE2. `initCodeSize` feeds the
EIP-3860 component of the success-flag re-check.
-/
structure PendingCreate where
  frame          : Frame
  stack          : Stack UInt256
  callerAccounts : AccountMap
  value          : UInt256
  initOffset     : UInt256
  initSize       : UInt256
  initCodeSize   : ℕ

/-- A suspended parent frame awaiting a child frame's result. -/
inductive Pending where
  | call   (pending : PendingCall)
  | create (pending : PendingCreate)

/--
The result of executing one instruction of a frame — what the instruction
signals back to the driver. Halting instructions emit `.halted` (with the
payload) directly.
-/
inductive Signal where
  /-- The frame continues with the updated execution state. -/
  | next (exec : ExecutionState)
  /-- The frame halted (normally, by revert, or exceptionally). -/
  | halted (halt : FrameHalt)
  /-- The instruction was a CALL-family instruction: suspend and descend. -/
  | needsCall (params : CallParams) (pending : PendingCall)
  /-- The instruction was CREATE/CREATE2: suspend and descend. -/
  | needsCreate (params : CreateParams) (pending : PendingCreate)

def FrameResult.toCallResult : FrameResult → CallResult
  | .call r   => r
  | .create r => r.toCallResult

def FrameResult.toCreateResult : FrameResult → CreateResult
  | .call r   => { toCallResult := r, address := 0 } -- unreachable pairing; the driver matches kinds
  | .create r => r

end Evm
