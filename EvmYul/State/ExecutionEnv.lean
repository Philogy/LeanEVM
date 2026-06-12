import EvmYul.Wheels
import EvmYul.Operations
import EvmYul.UInt256
import EvmYul.State.BlockHeader

namespace EvmYul

/--
The execution envorinment `I` `ExecutionEnv`. Section 9.3.
- `codeOwner` `Iₐ`
- `sender`    `Iₒ`
- `source`    `Iₛ`
- `weiValue`  `Iᵥ`
- `calldata` `I_d`
- `code`      `I_b`
- `gasPrice`  `Iₚ`
- `header`    `I_H`
- `depth`     `Iₑ`
- `perm`      `I_w`
-/
structure ExecutionEnv (τ : OperationType) where
  codeOwner : AccountAddress
  sender    : AccountAddress
  source    : AccountAddress
  weiValue  : UInt256
  calldata : ByteArray
  code      : ByteArray
  gasPrice  : ℕ
  header    : BlockHeader
  depth     : ℕ
  perm      : Bool
  blobVersionedHashes : List ByteArray
  deriving BEq, Inhabited, Repr

def prevRandao {τ} (e : ExecutionEnv τ) : UInt256 :=
  e.header.prevRandao

def basefee {τ} (e : ExecutionEnv τ) : UInt256 :=
  .ofNat e.header.baseFeePerGas

def ExecutionEnv.getBlobGasprice {τ} (e : ExecutionEnv τ) : UInt256 :=
  .ofNat e.header.getBlobGasprice

def blobhash {τ} (e : ExecutionEnv τ) (i : UInt256) : UInt256 :=
  e.blobVersionedHashes[i.toNat]?.option 0
    (.ofNat ∘ fromByteArrayBigEndian)

end EvmYul
