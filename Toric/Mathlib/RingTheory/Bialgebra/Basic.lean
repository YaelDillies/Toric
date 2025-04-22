import Mathlib.RingTheory.Bialgebra.Basic

open CoalgebraStruct Function

namespace Bialgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (A) in
lemma algebraMap_injective : Injective (algebraMap R A) := RightInverse.injective counit_algebraMap

lemma counit_surjective : Surjective (counit : A →ₗ[R] R) :=
  RightInverse.surjective counit_algebraMap

include R in
variable (R) in
/-- A bialgebra over a nontrivial ring is nontrivial. -/
lemma nontrivial [Nontrivial R] : Nontrivial A := (algebraMap_injective (R := R) _).nontrivial

end Bialgebra
