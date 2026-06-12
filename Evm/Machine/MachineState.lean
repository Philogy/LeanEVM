import Batteries

import Evm.Maps.ByteMap
import Evm.UInt256
import Batteries.Data.HashMap

namespace Evm

open Batteries

instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue  h₁ => isTrue <| congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse <| λ h ↦ by cases h; exact (h₂ rfl)

/--
The partial shared `MachineState` `μ`. Section 9.4.1.
- `gasAvailable` `g`
- `memory`       `m`
- `activeWords`  `i` - # active words.
- `returnData`   `o` - Data from the previous call from the current environment.

(The RETURN/REVERT payload is not machine state: the halting instruction
delivers it directly in its `Signal`.)
-/
structure MachineState where
  gasAvailable        : UInt256
  activeWords         : UInt256
  memory              : ByteArray
  returnData          : ByteArray
  deriving Inhabited

-- inductive WordSize := | Standard | Single

-- def WordSize.toNat (this : WordSize) : ℕ :=
--   match this with
--     | WordSize.Standard => 32
--     | WordSize.Single   => 1

-- instance : Coe WordSize Nat := ⟨WordSize.toNat⟩

end Evm
