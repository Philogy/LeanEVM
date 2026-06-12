import EvmYul.UInt256
open EvmYul UInt256
namespace T

def mulLimb (a : UInt256) (m : UInt32) : UInt256 :=
  let m64 := m.toUInt64
  let t0 := a.l0.toUInt64 * m64
  let t1 := a.l1.toUInt64 * m64 + (t0 >>> 32)
  let t2 := a.l2.toUInt64 * m64 + (t1 >>> 32)
  let t3 := a.l3.toUInt64 * m64 + (t2 >>> 32)
  let t4 := a.l4.toUInt64 * m64 + (t3 >>> 32)
  let t5 := a.l5.toUInt64 * m64 + (t4 >>> 32)
  let t6 := a.l6.toUInt64 * m64 + (t5 >>> 32)
  let t7 := a.l7.toUInt64 * m64 + (t6 >>> 32)
  ⟨t0.toUInt32, t1.toUInt32, t2.toUInt32, t3.toUInt32,
   t4.toUInt32, t5.toUInt32, t6.toUInt32, t7.toUInt32⟩

set_option maxHeartbeats 1000000 in
theorem mulLimb_toBitVec (a : UInt256) (m : UInt32) :
    (mulLimb a m).toBitVec = a.toBitVec * (BitVec.setWidth 256 m.toBitVec) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  simp [mulLimb, toBitVec]
  bv_decide (config := { timeout := 240, acNf := true })

end T
