import Mathlib.RingTheory.HopfAlgebra.Basic

export HopfAlgebraStruct (antipode)

namespace HopfAlgebra
variable {R A : Type*} [CommSemiring R]

section Semiring
variable [Semiring A] [HopfAlgebra R A]

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
