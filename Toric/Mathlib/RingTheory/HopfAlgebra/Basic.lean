import Mathlib.RingTheory.HopfAlgebra.Basic

export HopfAlgebraStruct (antipode)

namespace HopfAlgebra
variable {R A : Type*} [CommSemiring R]

section Semiring
variable [Semiring A] [HopfAlgebra R A]

lemma _root_.Coalgebra.Repr.algebraMap_counit_eq_sum_antipode_mul {a : A} (𝓡 : Coalgebra.Repr R a) :
    algebraMap R A (Coalgebra.counit a) =
      ∑ i ∈ 𝓡.index, antipode (R := R) (𝓡.left i) * 𝓡.right i := by simp [← 𝓡.eq]

lemma _root_.Coalgebra.Repr.algebraMap_counit_eq_sum_mul_antipode {a : A} (𝓡 : Coalgebra.Repr R a) :
    algebraMap R A (Coalgebra.counit a) =
      ∑ i ∈ 𝓡.index, 𝓡.left i * antipode (R := R) (𝓡.right i) := by simp [← 𝓡.eq]

lemma antipode_mul_antidistrib (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) b * antipode (R := R) a := by
  sorry

end Semiring

section CommRing
variable [CommSemiring A] [HopfAlgebra R A]

lemma antipode_mul_distrib (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) a * antipode (R := R) b := by
  rw [antipode_mul_antidistrib, mul_comm]

alias antipode_mul := antipode_mul_distrib

variable (R A) in
@[simps!]
def antipodeAlgHom : A →ₐ[R] A := .ofLinearMap antipode antipode_one antipode_mul

@[simp] lemma toLinearMap_antipodeAlgHom : (antipodeAlgHom R A).toLinearMap = antipode := rfl

end CommRing
end HopfAlgebra
