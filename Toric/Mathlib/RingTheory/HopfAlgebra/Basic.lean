import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# TODO

* Make `R` explicit in `antipode`.
* Unsimp and delete `sum_mul_antipode_eq`
-/

export HopfAlgebraStruct (antipode)

namespace HopfAlgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

lemma _root_.Coalgebra.Repr.algebraMap_counit_eq_sum_antipode_mul {a : A} (𝓡 : Coalgebra.Repr R a) :
    algebraMap R A (Coalgebra.counit a) =
      ∑ i ∈ 𝓡.index, antipode (R := R) (𝓡.left i) * 𝓡.right i := by simp [← 𝓡.eq]

lemma _root_.Coalgebra.Repr.algebraMap_counit_eq_sum_mul_antipode {a : A} (𝓡 : Coalgebra.Repr R a) :
    algebraMap R A (Coalgebra.counit a) =
      ∑ i ∈ 𝓡.index, 𝓡.left i * antipode (R := R) (𝓡.right i) := by simp [← 𝓡.eq]

end HopfAlgebra
