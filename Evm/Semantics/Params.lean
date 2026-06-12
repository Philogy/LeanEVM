import Evm.Maps.AccountMap
import Evm.State
import Evm.State.Substate
import Evm.UInt256

namespace Evm

/--
Parameters of a message call (the YP's `Θ`, eq. 119).

Field ↔ YP correspondence:
- `accounts` `σ`, `originalAccounts` `σ₀`, `substate` `A*`
- `caller` `s`, `origin` `Iₒ/o`, `recipient` `r`/`t`
- `codeSource` `c` — the code to run (or a precompile designator)
- `gas` `g`, `gasPrice` `p`, `value` `v`, `apparentValue` `v′`
- `calldata` `d`, `depth` `e`, `canModifyState` `w`
-/
structure CallParams where
  blobVersionedHashes : List ByteArray
  createdAccounts     : Batteries.RBSet AccountAddress compare
  genesisBlockHeader  : BlockHeader
  blocks              : ProcessedBlocks
  accounts            : AccountMap
  originalAccounts    : AccountMap
  substate            : Substate
  caller              : AccountAddress
  origin              : AccountAddress
  recipient           : AccountAddress
  codeSource          : ToExecute
  gas                 : UInt64
  gasPrice            : UInt256
  value               : UInt256
  apparentValue       : UInt256
  calldata            : ByteArray
  depth               : ℕ
  blockHeader         : BlockHeader
  chainId             : UInt256
  canModifyState      : Bool

/--
Result of a message call — the YP's `Θ` return tuple
`(createdAccounts, σ′, g′, A′, z, o)` as a named record.
-/
structure CallResult where
  createdAccounts : Batteries.RBSet AccountAddress compare
  accounts        : AccountMap
  gasRemaining    : UInt64
  substate        : Substate
  success         : Bool
  output          : ByteArray

/--
Parameters of contract creation (the YP's `Λ`, eq. 93).

`accounts` is the map the creation executes against — for the CREATE/CREATE2
opcodes the caller's nonce bump is already applied; `salt` distinguishes
CREATE2 (`some`) from CREATE (`none`).
-/
structure CreateParams where
  blobVersionedHashes : List ByteArray
  createdAccounts     : Batteries.RBSet AccountAddress compare
  genesisBlockHeader  : BlockHeader
  blocks              : ProcessedBlocks
  accounts            : AccountMap
  originalAccounts    : AccountMap
  substate            : Substate
  caller              : AccountAddress
  origin              : AccountAddress
  gas                 : UInt64
  gasPrice            : UInt256
  value               : UInt256
  initCode            : ByteArray
  depth               : ℕ
  salt                : Option ByteArray
  blockHeader         : BlockHeader
  chainId             : UInt256
  canModifyState      : Bool

/--
Result of contract creation — the YP's `Λ` return tuple with the derived
`address` of the (attempted) new contract. `output` is empty on success;
on revert it carries the revert data.
-/
structure CreateResult extends CallResult where
  address : AccountAddress

/--
Result of executing one transaction — the YP's `Υ` return tuple
`(σ′, A, z, gasUsed)` as a named record.
-/
structure TransactionResult where
  accounts : AccountMap
  substate : Substate
  success  : Bool
  gasUsed  : UInt64

end Evm
