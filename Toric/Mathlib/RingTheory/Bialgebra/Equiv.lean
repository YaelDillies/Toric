import Mathlib.RingTheory.Bialgebra.Equiv

open Function

namespace BialgEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- Promotes a bijective bialgebra homomorphism to a bialgebra equivalence. -/
noncomputable def ofBijective (f : A →ₐc[R] B) (hf : Function.Bijective f) : A ≃ₐc[R] B :=
  { AlgEquiv.ofBijective (f : A →ₐ[R] B) hf, f with }

@[simp]
theorem coe_ofBijective {f : A →ₐc[R] B} {hf : Function.Bijective f} :
    (BialgEquiv.ofBijective f hf : A → B) = f :=
  rfl

theorem ofBijective_apply {f : A →ₐc[R] B} {hf : Function.Bijective f} (a : A) :
    (BialgEquiv.ofBijective f hf) a = f a :=
  rfl

end BialgEquiv
