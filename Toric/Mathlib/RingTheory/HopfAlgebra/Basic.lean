import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# TODO

* Unsimp and delete `sum_mul_antipode_eq`
-/

export HopfAlgebraStruct (antipode)

open Coalgebra Bialgebra TensorProduct

namespace HopfAlgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

attribute [-simp] sum_antipode_mul_eq sum_mul_antipode_eq

lemma sum_counit_smul {a : A} (𝓡 : Repr R a) :
    ∑ x ∈ 𝓡.index, counit (R := R) (𝓡.left x) • 𝓡.right x = a := by
  have := sum_counit_tmul_eq  (R := R) 𝓡
  apply_fun lift (LinearMap.lsmul R A) at this
  simp_rw [map_sum] at this
  convert this
  simp

@[simp] lemma counit_antipode (a : A) : counit (R := R) (antipode R a) = counit a := by
  calc
        counit (antipode R a)
    _ = counit (∑ i ∈ (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) := by
      simp_rw [map_sum, counit_mul, ← smul_eq_mul, ← map_smul, ← map_sum, sum_counit_smul]
    _ = counit a := by simpa using congr(counit (R := R) $(sum_mul_antipode_eq_smul (ℛ R a)))

@[simp] lemma counit_comp_antipode : counit ∘ₗ antipode R = counit (A := A) := by
  ext; exact counit_antipode _

end HopfAlgebra
