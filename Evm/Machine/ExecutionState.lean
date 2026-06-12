import Evm.Machine.Stack

import Evm.State
import Evm.Machine.MachineState

namespace Evm

/--
The EVM execution state (world state + machine state + control state).
- `pc`    `pc`
- `stack` `s`
-/
structure ExecutionState extends Evm.State, Evm.MachineState where
  pc    : UInt32
  stack : Stack UInt256
  deriving Inhabited

end Evm
