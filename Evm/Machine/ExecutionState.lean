import Evm.Machine.Stack

import Evm.State
import Evm.Machine.SharedState

namespace Evm



/--
The EVM execution state (extends Evm.SharedState).
- `pc`         `pc`
- `stack`      `s`
- `stackSize`  - Cached `stack.length`, maintained by the interpreter via the
                 per-instruction net stack effect `α − δ` (the stack checks
                 would otherwise walk the list twice per executed instruction).
- `execLength` - Length of execution.
-/
structure ExecutionState extends Evm.SharedState where
  pc    : UInt256
  stack : Stack UInt256
  stackSize : ℕ
  execLength : ℕ
  deriving Inhabited

inductive ExecutionResult (S : Type) where
  | success (state : S) (o : ByteArray)
  | revert (g : UInt256) (o : ByteArray)



end Evm
