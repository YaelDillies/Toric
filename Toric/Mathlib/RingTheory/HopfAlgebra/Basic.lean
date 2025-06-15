import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# TODO

* Make `R` explicit in `antipode`.
* Unsimp and delete `sum_mul_antipode_eq`
-/

export HopfAlgebraStruct (antipode)

open Coalgebra Bialgebra TensorProduct

namespace HopfAlgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

lemma _root_.Coalgebra.Repr.algebraMap_counit_eq_sum_antipode_mul {a : A} (𝓡 : Coalgebra.Repr R a) :
    algebraMap R A (Coalgebra.counit a) =
      ∑ i ∈ 𝓡.index, antipode R (𝓡.left i) * 𝓡.right i := by simp [← 𝓡.eq]

lemma _root_.Coalgebra.Repr.algebraMap_counit_eq_sum_mul_antipode {a : A} (𝓡 : Coalgebra.Repr R a) :
    algebraMap R A (Coalgebra.counit a) =
      ∑ i ∈ 𝓡.index, 𝓡.left i * antipode R (𝓡.right i) := by simp [← 𝓡.eq]

lemma sum_counit_smul {a : A} (𝓡 : Coalgebra.Repr R a) :
    ∑ x ∈ 𝓡.index, counit (R := R) (𝓡.left x) • 𝓡.right x = a := by
  have := sum_counit_tmul_eq  (R := R) 𝓡
  apply_fun lift (LinearMap.lsmul R A) at this
  simp_rw [map_sum] at this
  convert this
  simp

lemma antipode_counit (a : A) : counit (R := R) (antipode R a) = counit (R := R) a := by
  have := sum_mul_antipode_eq_smul (R := R) (ℛ R a)
  apply_fun counit (R := R) at this
  simp_rw [map_smul, counit_one, smul_eq_mul, mul_one, map_sum, counit_mul, ← smul_eq_mul,
    ← map_smul, ← map_sum, sum_counit_smul (ℛ R a)] at this
  exact this

end HopfAlgebra
