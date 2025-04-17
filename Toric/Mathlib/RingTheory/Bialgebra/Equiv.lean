import Mathlib.RingTheory.Bialgebra.Equiv
import Toric.Mathlib.RingTheory.Bialgebra.Hom

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

/-- The bialgebra equivalence defined by a bijective bialgebra hom. -/
@[simps!]
noncomputable def ofBialgHom (f :  A →ₐc[R] B) (hf : Bijective f) :  A ≃ₐc[R] B where
  toFun a := f a
  map_add' := f.map_add'
  map_smul' := f.map_smul'
  counit_comp := f.counit_comp
  map_comp_comul := f.map_comp_comul
  invFun := Function.surjInv hf.surjective
  left_inv := Function.leftInverse_surjInv hf
  right_inv := Function.rightInverse_surjInv _
  map_mul' := f.map_mul'

/-- Promotes a bijective coalgebra homomorphism to a coalgebra equivalence. -/
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
