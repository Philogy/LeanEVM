import Evm.State
import Evm.MachineState

namespace Evm

structure SharedState extends Evm.State, Evm.MachineState
  deriving Inhabited

end Evm
