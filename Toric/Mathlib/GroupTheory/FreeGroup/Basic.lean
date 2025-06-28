import Mathlib.GroupTheory.FreeGroup.Basic

variable {α M : Type*} [Monoid M]

@[ext high]
lemma FreeGroup.ext_hom' {f g : FreeGroup α →* M} (h : ∀ (a : α), f (of a) = g (of a)) : f = g := by
  ext x
  have (x) : f ((of x)⁻¹) = g ((of x)⁻¹) := by
    trans f ((of x)⁻¹) * f (of x) * g ((of x)⁻¹)
    · simp_rw [mul_assoc, h, ← _root_.map_mul, mul_inv_cancel, _root_.map_one, mul_one]
    · simp_rw [← _root_.map_mul, inv_mul_cancel, _root_.map_one, one_mul]
  induction x <;> simp [*, instMonad]
