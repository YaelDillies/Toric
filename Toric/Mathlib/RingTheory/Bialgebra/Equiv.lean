import Mathlib.RingTheory.Bialgebra.Equiv

open Coalgebra Function TensorProduct

namespace BialgEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- Construct a bialgebra hom from an algebra hom respecting counit and comultiplication. -/
@[simps] def ofAlgEquiv (f : A ≃ₐ[R] B) (counit_comp : counit ∘ₗ f.toLinearMap = counit)
    (map_comp_comul : map f.toLinearMap f.toLinearMap ∘ₗ comul = comul ∘ₗ f.toLinearMap) :
    A ≃ₐc[R] B where
  __ := f
  map_smul' := map_smul f
  counit_comp := counit_comp
  map_comp_comul := map_comp_comul

/-- Construct a coalgebra equivalence from a bijective coalgebra homomorphism. -/
noncomputable def ofBijective (f : A →ₐc[R] B) (hf : Function.Bijective f) : A ≃ₐc[R] B :=
  { AlgEquiv.ofBijective (f : A →ₐ[R] B) hf, f with }

@[simp]
theorem apply_symm_apply (e : A ≃ₐc[R] B) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A ≃ₐc[R] B) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

@[simp]
theorem comp_sym (e : A ≃ₐc[R] B) : BialgHom.comp (e : A →ₐc[R] B) ↑e.symm = BialgHom.id R B := by
  ext
  simp

@[simp]
theorem symm_comp (e : A ≃ₐc[R] B) : BialgHom.comp ↑e.symm (e : A →ₐc[R] B) = BialgHom.id R A := by
  ext
  simp

@[simp]
theorem coe_ofBijective {f : A →ₐc[R] B} {hf : Function.Bijective f} :
    (BialgEquiv.ofBijective f hf : A → B) = f :=
  rfl

theorem ofBijective_apply {f : A →ₐc[R] B} {hf : Function.Bijective f} (a : A) :
    (BialgEquiv.ofBijective f hf) a = f a :=
  rfl

end BialgEquiv
