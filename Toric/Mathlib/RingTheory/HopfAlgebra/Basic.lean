import Mathlib.RingTheory.HopfAlgebra.Basic

namespace HopfAlgebra
variable {R A : Type*} [CommRing R]

section Semiring
variable [Semiring A] [HopfAlgebra R A]

lemma antipode_mul_antidistrib (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) b * antipode (R := R) a := by
  sorry

end Semiring

section CommRing
variable [CommRing A] [HopfAlgebra R A]

lemma antipode_mul_distrib (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) a * antipode (R := R) b := by
  rw [antipode_mul_antidistrib, mul_comm]

end CommRing
end HopfAlgebra
