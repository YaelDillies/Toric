import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# TODO

More explicit arguments to `BialgEquiv.ofBijective`
-/

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

@[simp]
lemma apply_symm_apply (e : A ≃ₐc[R] B) : ∀ x, e (e.symm x) = x := e.toEquiv.apply_symm_apply

@[simp]
lemma symm_apply_apply (e : A ≃ₐc[R] B) : ∀ x, e.symm (e x) = x := e.toEquiv.symm_apply_apply

@[simp] lemma comp_symm (e : A ≃ₐc[R] B) : (e : A →ₐc[R] B).comp e.symm = .id R B := by ext; simp
@[simp] lemma symm_comp (e : A ≃ₐc[R] B) : (e.symm : B →ₐc[R] A).comp e = .id R A := by ext; simp

end BialgEquiv
