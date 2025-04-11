import Mathlib.LinearAlgebra.PerfectPairing.Basic

namespace PerfectPairing

-- Make `PerfectPairing` a class
attribute [class] PerfectPairing

-- Use scalar product notation for the bilinear map in perfect pairings
scoped[PerfectPairing] notation3 "⟪" x ", " y "⟫_" K:max =>
  PerfectPairing.toLin (R := K) inferInstance x y

variable {R N M : Type*}
variable [CommRing R] [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
variable [inst : PerfectPairing R N M]

instance instFlip : PerfectPairing R M N := inst.flip

-- probably bad names, as it isn't really an inner product
lemma inner_comm (x : N) (y : M) : ⟪x, y⟫_R = ⟪y, x⟫_R := rfl

lemma inner_add_left (x y : N) (z : M) : ⟪x+y, z⟫_R = ⟪x, z⟫_R + ⟪y, z⟫_R := by rw [map_add]; rfl

lemma inner_add_right (x : N) (y z : M) : ⟪x, y+z⟫_R = ⟪x, y⟫_R + ⟪x, z⟫_R := map_add _ y z

lemma inner_zero_left (x : M) : ⟪(0 : N), x⟫_R = 0 := by simp

lemma inner_zero_right (x : N) : ⟪x, (0 : M)⟫_R = 0 := by simp

lemma inner_smul_left (r : R) (x : N) (y : M) : ⟪r • x, y⟫_R = r * ⟪x, y⟫_R := by simp

lemma inner_smul_right (r : R) (x : N) (y : M) : ⟪x, r • y⟫_R = r * ⟪x, y⟫_R := by simp

end PerfectPairing
