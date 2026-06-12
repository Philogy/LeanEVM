import Evm.Machine.SharedState
import Evm.StateOps
import Evm.Machine.MachineStateOps
import Evm.Machine.MachineState
import Evm.Operations
import Mathlib.Data.List.Intervals

namespace Evm

namespace SharedState

section Memory

def calldatacopy (self : SharedState) (mstart datastart size : UInt256) : SharedState :=
  { self with
    memory := self.executionEnv.calldata.write datastart.toNat self.memory mstart.toNat size.toNat
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }

def codeCopy  (self : SharedState) (mstart cstart size : UInt256) : SharedState :=
  { self with
    memory := self.executionEnv.code.write cstart.toNat self.memory mstart.toNat size.toNat
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }

def extCodeCopy' (self : SharedState) (acc mstart cstart size : UInt256) : SharedState :=
  let mstart := mstart.toNat
  let cstart := cstart.toNat
  let size := size.toNat
  let addr := AccountAddress.ofUInt256 acc
  let b : ByteArray := self.toState.lookupAccount addr |>.option .empty (·.code)
  { self with
    memory := b.write cstart self.memory mstart size
    substate := .addAccessedAccount self.toState.substate addr
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart size)
  }

end Memory

def logOp (offset size : UInt256) (t : Array UInt256) (sState : SharedState) : SharedState :=
  let self := sState.executionEnv.address
  let mem := sState.memory.readWithPadding offset.toNat size.toNat
  { sState with
    substate.logSeries := sState.substate.logSeries.push ⟨self, t, mem⟩
    activeWords := .ofNat (MachineState.M sState.activeWords.toNat offset.toNat size.toNat)
  }

end SharedState

end Evm
