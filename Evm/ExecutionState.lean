import Evm.Data.Stack

import Evm.State
import Evm.SharedState

namespace Evm



/--
The EVM execution state (extends Evm.SharedState).
- `pc`         `pc`
- `stack`      `s`
- `execLength` - Length of execution.
-/
structure ExecutionState extends Evm.SharedState where
  pc    : UInt256
  stack : Stack UInt256
  execLength : ℕ
  deriving Inhabited

inductive ExecutionResult (S : Type) where
  | success (state : S) (o : ByteArray)
  | revert (g : UInt256) (o : ByteArray)



end Evm
