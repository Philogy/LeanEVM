import Evm.UInt256
import Evm.Wheels

namespace Evm

/--
`BlockHeader`. `H_<x>`. Section 4.3.

`parentHash`    `p`
`ommersHash`    `o`
`beneficiary`   `c`
`stateRoot`     `r`
`transRoot`     `t`
`receiptRoot`   `e`
`logsBloom`     `b`
`difficulty`    `d` [deprecated]
`number`        `i`
`gasLimit`      `l`
`gasUsed`       `g`
`timestamp`     `s`
`extraData`     `x`
`chainId`       `n` 
`nonce`         `n` [deprecated]
`baseFeePerGas` `f`
`withdrawalsRoot` (EIP-4895)
`parentBeaconBlockRoot` (EIP-4877)
-/
structure BlockHeader where
  parentHash    : UInt256
  ommersHash    : UInt256
  beneficiary   : AccountAddress
  stateRoot     : UInt256
  transRoot     : ByteArray
  receiptRoot   : ByteArray
  logsBloom     : ByteArray
  -- Officially deprecated, but checked in `wrongDifficulty_Cancun`
  difficulty    : ℕ
  number        : ℕ
  gasLimit      : ℕ
  gasUsed       : ℕ
  timestamp     : ℕ
  extraData     : ByteArray
  nonce         : UInt64
  prevRandao    : UInt256
  baseFeePerGas : ℕ
  parentBeaconBlockRoot : ByteArray
  withdrawalsRoot : ByteArray
  blobGasUsed     : UInt64
  excessBlobGas   : UInt64
deriving DecidableEq, Inhabited, Repr, BEq

def prettyDifference (h₁ h₂ : BlockHeader) : String := Id.run do
  let mut result := ""
  if h₁.parentHash != h₂.parentHash then result := result ++ "different parentHash\n"
  if h₁.ommersHash != h₂.ommersHash then result := result ++ "different ommersHash\n"
  if h₁.beneficiary != h₂.beneficiary then result := result ++ "different beneficiary\n"
  if h₁.stateRoot != h₂.stateRoot then result := result ++ "different stateRoot\n"
  if h₁.transRoot != h₂.transRoot then result := result ++ "different transRoot\n"
  if h₁.receiptRoot != h₂.receiptRoot then result := result ++ "different receiptRoot\n"
  if h₁.logsBloom != h₂.logsBloom then result := result ++ "different logsBloom\n"
  if h₁.difficulty != h₂.difficulty then result := result ++ "different difficulty\n"
  if h₁.number != h₂.number then result := result ++ "different number\n"
  if h₁.gasLimit != h₂.gasLimit then result := result ++ "different gasLimit\n"
  if h₁.gasUsed != h₂.gasUsed then result := result ++ "different gasUsed\n"
  if h₁.timestamp != h₂.timestamp then result := result ++ "different timestamp\n"
  if h₁.extraData != h₂.extraData then result := result ++ "different extraData\n"
  if h₁.nonce != h₂.nonce then result := result ++ "different nonce\n"
  if h₁.prevRandao != h₂.prevRandao then result := result ++ "different prevRandao\n"
  if h₁.baseFeePerGas != h₂.baseFeePerGas then result := result ++ "different baseFeePerGas\n"
  if h₁.parentBeaconBlockRoot != h₂.parentBeaconBlockRoot then result := result ++ "different parentBeaconBlockRoot\n"
  if h₁.withdrawalsRoot != h₂.withdrawalsRoot then result := result ++ "different withdrawalsRoot\n"
  if h₁.blobGasUsed != h₂.blobGasUsed then result := result ++ "different blobGasUsed\n"
  if h₁.excessBlobGas != h₂.excessBlobGas then result := result ++ "different excessBlobGas\n"

  result

def TARGET_BLOB_GAS_PER_BLOCK := 393216

def calcExcessBlobGas (parent : BlockHeader) : Option UInt64 := do
  if parent.excessBlobGas.toNat + parent.blobGasUsed.toNat < TARGET_BLOB_GAS_PER_BLOCK then
    pure 0
  else
    pure <| .ofNat <| parent.excessBlobGas.toNat + parent.blobGasUsed.toNat - TARGET_BLOB_GAS_PER_BLOCK

-- See https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
partial def fakeExponential0 (i output factor numerator denominator : ℕ) : (numeratorAccum : ℕ) → ℕ
  | 0 =>
    output / denominator
  | numeratorAccum =>
    let output := output + numeratorAccum
    let numeratorAccum := (numeratorAccum * numerator) / (denominator * i)
    let i := i + 1
    fakeExponential0 i output factor numerator denominator numeratorAccum

def fakeExponential (factor numerator denominator : ℕ) : ℕ :=
  fakeExponential0 1 0 factor numerator denominator (factor * denominator)

def MIN_BASE_FEE_PER_BLOB_GAS := 1
def BLOB_BASE_FEE_UPDATE_FRACTION := 3338477

def BlockHeader.getBlobGasprice (h : BlockHeader) : ℕ :=
  fakeExponential
    MIN_BASE_FEE_PER_BLOB_GAS
    h.excessBlobGas.toNat
    BLOB_BASE_FEE_UPDATE_FRACTION

end Evm
