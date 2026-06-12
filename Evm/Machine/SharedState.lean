import Evm.State
import Evm.Machine.MachineState

namespace Evm

structure SharedState extends Evm.State, Evm.MachineState
  deriving Inhabited

end Evm
