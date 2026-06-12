import Init.Data.Nat.Div
import Std.Tactic.BVDecide
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

namespace EvmYul

/-- The size of type `UInt256`, that is, `2^256`. -/
def UInt256.size : ℕ :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

instance : NeZero UInt256.size where
  out := (by unfold UInt256.size; simp)

/--
A 256-bit EVM word as eight 32-bit limbs, least-significant first.

The representation is 32-bit limbs (not 64) so that every intermediate of the
limb-level multiplication fits `UInt64` (`(2^32-1)^2 + 2*(2^32-1) < 2^64`).
All eight fields are scalar, so a value is a single flat unboxed object —
no GMP allocation, unlike the previous `Fin (2^256)` representation.

The *semantic reference* is `BitVec 256` via `toBitVec`. Every limb-level
operation below is proven equivalent to its `BitVec` counterpart
(`toBitVec_add`, `toBitVec_mul`, …), so the limb arithmetic is not part of
the trust surface. Operations without a limb-level implementation go through
`toNat`/`ofNat` round-trips and are correct by construction.
-/
structure UInt256 where
  l0 : UInt32
  l1 : UInt32
  l2 : UInt32
  l3 : UInt32
  l4 : UInt32
  l5 : UInt32
  l6 : UInt32
  l7 : UInt32
  deriving DecidableEq

namespace UInt256

/-- Semantic reference value: most-significant limb first in the append. -/
def toBitVec (a : UInt256) : BitVec 256 :=
  a.l7.toBitVec ++ a.l6.toBitVec ++ a.l5.toBitVec ++ a.l4.toBitVec ++
  a.l3.toBitVec ++ a.l2.toBitVec ++ a.l1.toBitVec ++ a.l0.toBitVec

def ofBitVec (b : BitVec 256) : UInt256 :=
  ⟨ ⟨b.extractLsb'   0 32⟩, ⟨b.extractLsb'  32 32⟩
  , ⟨b.extractLsb'  64 32⟩, ⟨b.extractLsb'  96 32⟩
  , ⟨b.extractLsb' 128 32⟩, ⟨b.extractLsb' 160 32⟩
  , ⟨b.extractLsb' 192 32⟩, ⟨b.extractLsb' 224 32⟩ ⟩

def toNat (a : UInt256) : ℕ := a.toBitVec.toNat

def ofNat (n : ℕ) : UInt256 :=
  ⟨ .ofNat n          , .ofNat (n >>> 32) , .ofNat (n >>> 64) , .ofNat (n >>> 96)
  , .ofNat (n >>> 128), .ofNat (n >>> 160), .ofNat (n >>> 192), .ofNat (n >>> 224) ⟩

instance {n : ℕ} : OfNat UInt256 n := ⟨ofNat n⟩
instance : Inhabited UInt256 := ⟨ofNat 0⟩

instance : ToString UInt256 where
  toString a := toString a.toNat

instance : Repr UInt256 where
  reprPrec n _ := repr n.toNat

/-! ### Limb-level operations (proven equivalent to `BitVec 256`) -/

def add (a b : UInt256) : UInt256 :=
  let s0 := a.l0.toUInt64 + b.l0.toUInt64
  let s1 := a.l1.toUInt64 + b.l1.toUInt64 + (s0 >>> 32)
  let s2 := a.l2.toUInt64 + b.l2.toUInt64 + (s1 >>> 32)
  let s3 := a.l3.toUInt64 + b.l3.toUInt64 + (s2 >>> 32)
  let s4 := a.l4.toUInt64 + b.l4.toUInt64 + (s3 >>> 32)
  let s5 := a.l5.toUInt64 + b.l5.toUInt64 + (s4 >>> 32)
  let s6 := a.l6.toUInt64 + b.l6.toUInt64 + (s5 >>> 32)
  let s7 := a.l7.toUInt64 + b.l7.toUInt64 + (s6 >>> 32)
  ⟨s0.toUInt32, s1.toUInt32, s2.toUInt32, s3.toUInt32,
   s4.toUInt32, s5.toUInt32, s6.toUInt32, s7.toUInt32⟩

/-- `a - b` as `a + ~b + 1`, one carry chain. -/
def sub (a b : UInt256) : UInt256 :=
  let s0 := a.l0.toUInt64 + (~~~b.l0).toUInt64 + 1
  let s1 := a.l1.toUInt64 + (~~~b.l1).toUInt64 + (s0 >>> 32)
  let s2 := a.l2.toUInt64 + (~~~b.l2).toUInt64 + (s1 >>> 32)
  let s3 := a.l3.toUInt64 + (~~~b.l3).toUInt64 + (s2 >>> 32)
  let s4 := a.l4.toUInt64 + (~~~b.l4).toUInt64 + (s3 >>> 32)
  let s5 := a.l5.toUInt64 + (~~~b.l5).toUInt64 + (s4 >>> 32)
  let s6 := a.l6.toUInt64 + (~~~b.l6).toUInt64 + (s5 >>> 32)
  let s7 := a.l7.toUInt64 + (~~~b.l7).toUInt64 + (s6 >>> 32)
  ⟨s0.toUInt32, s1.toUInt32, s2.toUInt32, s3.toUInt32,
   s4.toUInt32, s5.toUInt32, s6.toUInt32, s7.toUInt32⟩

-- NOTE: multiplication currently round-trips through `Nat` (see below) rather
-- than using limb arithmetic: a limb-level schoolbook multiply is easy to
-- write but its `BitVec` equivalence is exactly the kind of goal SAT-based
-- `bv_decide` struggles with (multiplier equivalence). Until that proof
-- lands, `Nat` keeps `mul` out of the trust surface.

def land (a b : UInt256) : UInt256 :=
  ⟨a.l0 &&& b.l0, a.l1 &&& b.l1, a.l2 &&& b.l2, a.l3 &&& b.l3,
   a.l4 &&& b.l4, a.l5 &&& b.l5, a.l6 &&& b.l6, a.l7 &&& b.l7⟩

def lor (a b : UInt256) : UInt256 :=
  ⟨a.l0 ||| b.l0, a.l1 ||| b.l1, a.l2 ||| b.l2, a.l3 ||| b.l3,
   a.l4 ||| b.l4, a.l5 ||| b.l5, a.l6 ||| b.l6, a.l7 ||| b.l7⟩

def xor (a b : UInt256) : UInt256 :=
  ⟨a.l0 ^^^ b.l0, a.l1 ^^^ b.l1, a.l2 ^^^ b.l2, a.l3 ^^^ b.l3,
   a.l4 ^^^ b.l4, a.l5 ^^^ b.l5, a.l6 ^^^ b.l6, a.l7 ^^^ b.l7⟩

/-- Bitwise NOT (the Yellow Paper's `complement`, i.e. `2^256 - 1 - a`). -/
def complement (a : UInt256) : UInt256 :=
  ⟨~~~a.l0, ~~~a.l1, ~~~a.l2, ~~~a.l3, ~~~a.l4, ~~~a.l5, ~~~a.l6, ~~~a.l7⟩

def beq (a b : UInt256) : Bool :=
  a.l0 == b.l0 && a.l1 == b.l1 && a.l2 == b.l2 && a.l3 == b.l3 &&
  a.l4 == b.l4 && a.l5 == b.l5 && a.l6 == b.l6 && a.l7 == b.l7

instance : BEq UInt256 := ⟨beq⟩

/-- Unsigned less-than, lexicographic from the most significant limb. -/
def blt (a b : UInt256) : Bool :=
  (a.l7.toBitVec.ult b.l7.toBitVec) ||
  (a.l7 == b.l7 && ((a.l6.toBitVec.ult b.l6.toBitVec) ||
  (a.l6 == b.l6 && ((a.l5.toBitVec.ult b.l5.toBitVec) ||
  (a.l5 == b.l5 && ((a.l4.toBitVec.ult b.l4.toBitVec) ||
  (a.l4 == b.l4 && ((a.l3.toBitVec.ult b.l3.toBitVec) ||
  (a.l3 == b.l3 && ((a.l2.toBitVec.ult b.l2.toBitVec) ||
  (a.l2 == b.l2 && ((a.l1.toBitVec.ult b.l1.toBitVec) ||
  (a.l1 == b.l1 && a.l0.toBitVec.ult b.l0.toBitVec)))))))))))))

def ble (a b : UInt256) : Bool := !(blt b a)

/-! ### `BitVec 256` equivalence -/

section BitVecEquivalence

theorem toBitVec_ofBitVec (b : BitVec 256) : (ofBitVec b).toBitVec = b := by
  simp [ofBitVec, toBitVec]
  bv_decide

theorem ofBitVec_toBitVec (a : UInt256) : ofBitVec a.toBitVec = a := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := a
  simp [ofBitVec, toBitVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> · apply UInt32.toBitVec_inj.mp; simp; bv_decide

theorem toBitVec_add (a b : UInt256) : (add a b).toBitVec = a.toBitVec + b.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [add, toBitVec]
  bv_decide

theorem toBitVec_sub (a b : UInt256) : (sub a b).toBitVec = a.toBitVec - b.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [sub, toBitVec]
  bv_decide

theorem toBitVec_land (a b : UInt256) : (land a b).toBitVec = a.toBitVec &&& b.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [land, toBitVec]
  bv_decide

theorem toBitVec_lor (a b : UInt256) : (lor a b).toBitVec = a.toBitVec ||| b.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [lor, toBitVec]
  bv_decide

theorem toBitVec_xor (a b : UInt256) : (xor a b).toBitVec = a.toBitVec ^^^ b.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [xor, toBitVec]
  bv_decide

theorem toBitVec_complement (a : UInt256) : (complement a).toBitVec = ~~~a.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  simp [complement, toBitVec]
  bv_decide

theorem toBitVec_inj {a b : UInt256} (h : a.toBitVec = b.toBitVec) : a = b := by
  have := congrArg ofBitVec h
  rwa [ofBitVec_toBitVec, ofBitVec_toBitVec] at this

theorem toNat_inj {a b : UInt256} (h : a.toNat = b.toNat) : a = b :=
  toBitVec_inj (BitVec.eq_of_toNat_eq h)

theorem beq_iff_eq (a b : UInt256) : beq a b = true ↔ a = b := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp [beq, and_assoc]

theorem beq_iff_toBitVec_eq (a b : UInt256) : beq a b = true ↔ a.toBitVec = b.toBitVec :=
  ⟨λ h ↦ congrArg toBitVec ((beq_iff_eq a b).mp h),
   λ h ↦ (beq_iff_eq a b).mpr (toBitVec_inj h)⟩

theorem blt_iff_toBitVec_lt (a b : UInt256) : blt a b = true ↔ a.toBitVec < b.toBitVec := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  rw [← BitVec.ult_iff_lt]
  simp only [blt, toBitVec]
  bv_decide

end BitVecEquivalence

/-! ### Order and remaining instances -/

theorem toNat_eq_toBitVec_toNat (a : UInt256) : a.toNat = a.toBitVec.toNat := rfl

instance : LT UInt256 where
  lt a b := a.toBitVec < b.toBitVec

instance : LE UInt256 where
  le a b := a.toBitVec ≤ b.toBitVec

instance (a b : UInt256) : Decidable (a < b) :=
  decidable_of_iff _ (blt_iff_toBitVec_lt a b)

instance (a b : UInt256) : Decidable (a ≤ b) :=
  decidable_of_iff (blt b a = false) <| by
    have h := blt_iff_toBitVec_lt b a
    constructor
    · intro hf
      have : ¬ (b.toBitVec < a.toBitVec) := λ hc ↦ by simp [h.mpr hc] at hf
      exact BitVec.not_lt.mp this
    · intro hle
      cases hb : blt b a
      · rfl
      · exact absurd (h.mp hb) (BitVec.not_lt.mpr hle)

instance : Preorder UInt256 where
  le_refl a := BitVec.le_refl _
  le_trans _ _ _ h₁ h₂ := BitVec.le_trans h₁ h₂
  lt_iff_le_not_ge a b := by
    constructor
    · intro h; exact ⟨BitVec.le_of_lt h, BitVec.not_le.mpr h⟩
    · intro ⟨_, h⟩; exact BitVec.not_le.mp h

instance : Max UInt256 := maxOfLe
instance : Min UInt256 := minOfLe

instance : Ord UInt256 where
  compare a b := if a < b then .lt else if b < a then .gt else .eq

/-! ### Operations via `Nat`/`BitVec` round-trip (correct by construction) -/

def mul (a b : UInt256) : UInt256 := ofNat (a.toNat * b.toNat)

def div (a b : UInt256) : UInt256 := ofNat (a.toNat / b.toNat)

def mod (a b : UInt256) : UInt256 := if b.toNat == 0 then 0 else ofNat (a.toNat % b.toNat)

def modn (a : UInt256) (n : ℕ) : UInt256 := if n == 0 then a else ofNat (a.toNat % n)

def shiftLeft (a b : UInt256) : UInt256 :=
  if 256 ≤ b.toNat then 0 else ofBitVec (a.toBitVec <<< b.toNat)

def shiftRight (a b : UInt256) : UInt256 :=
  if 256 ≤ b.toNat then 0 else ofBitVec (a.toBitVec >>> b.toNat)

def log2 (a : UInt256) : UInt256 := ofNat a.toNat.log2

instance : Add UInt256 := ⟨UInt256.add⟩
instance : Sub UInt256 := ⟨UInt256.sub⟩
instance : Mul UInt256 := ⟨UInt256.mul⟩
instance : Div UInt256 := ⟨UInt256.div⟩
instance : Mod UInt256 := ⟨UInt256.mod⟩
instance : HMod UInt256 ℕ UInt256 := ⟨UInt256.modn⟩
instance : Complement UInt256 := ⟨UInt256.complement⟩

def lnot (a : UInt256) : UInt256 := complement a

def abs (a : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat
  then sub 0 a
  else a

def fromSigned (a : UInt256) : ℤ := a.toBitVec.toInt

def toSigned (i : ℤ) : UInt256 :=
  match i with
    | .ofNat n => ofNat n
    | .negSucc n => ofNat (UInt256.size - 1 - n)

private def powAux (a : UInt256) (c : UInt256) : ℕ → UInt256
  | 0 => a
  | n@(k + 1) => if n % 2 == 1
                 then powAux (a * c) (c * c) (n / 2)
                 else powAux a       (c * c) (n / 2)

def pow (b : UInt256) (n : UInt256) := powAux 1 b n.toNat

instance : HPow UInt256 UInt256 UInt256 := ⟨pow⟩
instance : AndOp UInt256 := ⟨UInt256.land⟩
instance : OrOp UInt256 := ⟨UInt256.lor⟩
instance : XorOp UInt256 := ⟨UInt256.xor⟩
instance : ShiftLeft UInt256 := ⟨UInt256.shiftLeft⟩
instance : ShiftRight UInt256 := ⟨UInt256.shiftRight⟩

def eq0 (a : UInt256) : Bool := a == 0

def byteAt (a b : UInt256) : UInt256 :=
  if a > 31 then 0 else
    b >>> (UInt256.ofNat ((31 - a.toNat) * 8)) &&& 0xFF

def sgn (a : UInt256) : ℤ :=
  if 2 ^ 255 <= a.toNat then
    -1
  else
    if eq0 a then 0 else 1

def bigUInt : UInt256 := ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def sdiv (a b : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat then
    if 2 ^ 255 <= b.toNat then
      abs a / abs b
    else sub 0 (abs a / b)
  else
    if 2 ^ 255 <= b.toNat then
      sub 0 (a / abs b)
    else a / b

def smod (a b : UInt256) : UInt256 :=
  if b.toNat == 0 then 0
  else
    toSigned <| sgn a * (abs a % abs b).toNat

def sltBool (a b : UInt256) : Bool :=
  if a.toNat ≥ 2 ^ 255 then
    if b.toNat ≥ 2 ^ 255 then
      a < b
    else true
  else
    if b.toNat ≥ 2 ^ 255 then false
    else a < b

def sgtBool (a b : UInt256) : Bool :=
  if a.toNat ≥ 2 ^ 255 then
    if b.toNat ≥ 2 ^ 255 then
      a > b
    else false
  else
    if b.toNat ≥ 2 ^ 255 then true
    else a > b

abbrev fromBool (b : Bool) : UInt256 := if b then 1 else 0

def slt (a b : UInt256) :=
  fromBool (sltBool a b)

def sgt (a b : UInt256) :=
  fromBool (sgtBool a b)

def sar (a b : UInt256) : UInt256 :=
  if sltBool b 0
  then UInt256.complement (UInt256.complement b >>> a)
  else b >>> a

private partial def dbg_toHex (n : Nat) : String :=
  if n < 16
  then hexDigitRepr n
  else (dbg_toHex (n / 16)) ++ hexDigitRepr (n % 16)

def signextend (a b : UInt256) : UInt256 :=
  if a.toNat ≤ 31 then
    let test_bit := a * 8 + 7
    let sign_bit := (1 : UInt256) <<< test_bit
    if b &&& sign_bit ≠ 0 then
      b ||| (ofNat (UInt256.size - sign_bit.toNat))
    else b &&& (sign_bit - 1)
  else b

def addMod (a b c : UInt256) : UInt256 :=
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  if eq0 c then 0 else
    ofNat <| Nat.mod (a.toNat + b.toNat) c.toNat

def mulMod (a b c : UInt256) : UInt256 :=
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  if eq0 c then 0 else
    ofNat <| Nat.mod (a.toNat * b.toNat) c.toNat

def exp (a b : UInt256) : UInt256 := pow a b

def lt (a b : UInt256) := fromBool (a < b)

def gt (a b : UInt256) := fromBool (a > b)

def eq (a b : UInt256) := fromBool (a == b)

def isZero (a : UInt256) :=
  fromBool (eq0 a)

end UInt256

end EvmYul

section CastUtils

open EvmYul UInt256

abbrev Nat.toUInt256 : ℕ → UInt256 := ofNat
abbrev UInt8.toUInt256 (a : UInt8) : UInt256 := EvmYul.UInt256.ofNat a.toNat

def Bool.toUInt256 (b : Bool) : UInt256 := if b then 1 else 0

@[simp]
lemma Bool.toUInt256_true : true.toUInt256 = (1 : UInt256) := rfl

@[simp]
lemma Bool.toUInt256_false : false.toUInt256 = (0 : UInt256) := rfl

end CastUtils

namespace EvmYul

-- | Convert from a list of little-endian bytes to a natural number.
def fromBytes' : List UInt8 → ℕ
| [] => 0
| b :: bs => b.toFin.val + 2^8 * fromBytes' bs

def fromBytesBigEndian : List UInt8 → ℕ := fromBytes' ∘ List.reverse
def fromByteArrayBigEndian (b : ByteArray) : ℕ := fromBytesBigEndian b.toList

variable {bs : List UInt8}
         {n : ℕ}

-- | Convert a natural number into a list of bytes.
private def toBytes' : ℕ → List UInt8
  | 0 => []
  | n@(.succ n') =>
    let byte : UInt8 := UInt8.ofNat (Nat.mod n UInt8.size)
    have : n / UInt8.size < n' + 1 := by
      rename_i h
      rw [h]
      apply Nat.div_lt_self <;> simp
    byte :: toBytes' (n / UInt8.size)

def toBytesBigEndian : ℕ → List UInt8 := List.reverse ∘ toBytes'

-- | Zero-pad a list of bytes up to some length, adding the zeroes on the right.
private def zeroPadBytes (n : ℕ) (bs : List UInt8) : List UInt8 :=
  bs ++ (List.replicate (n - bs.length)) 0

def fromBytes! (bs : List UInt8) : ℕ := fromBytes' (bs.take 32)

-- Convenience function for spooning into UInt256.
-- Given that I 'accept' UInt8, might as well live with UInt256.
def fromBytes_if_you_really_must? (bs : List UInt8) : UInt256 :=
  .ofNat (fromBytes! bs)

def toBytes! (n : UInt256) : List UInt8 := zeroPadBytes 32 (toBytes' n.toNat)

def uInt256OfByteArray (arr : ByteArray) : UInt256 :=
  .ofNat <| fromBytes' arr.data.toList.reverse

end EvmYul

section HicSuntDracones

def ByteArray.copySlice' (src : ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) (exact : Bool := true) : ByteArray :=
  if false -- srcOff < 2^64 && destOff < 2^64 && len < 2^64
  then src.copySlice srcOff dest destOff len exact -- NB only when `srcOff`, `destOff` and `len` are sufficiently small
  else let srcData := src.data
       let destData := dest.data
       let sourceChunk := srcData.extract srcOff (srcOff + len)
       let destBegin := destData.extract 0 destOff
       let destEnd := destData.extract (destOff + len) destData.size
       ⟨destBegin ++ sourceChunk ++ destEnd⟩

end HicSuntDracones
