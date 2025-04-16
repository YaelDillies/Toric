import Mathlib.RingTheory.Bialgebra.Equiv

open Function

namespace BialgEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

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
  map_mul' :=f.map_mul'

end BialgEquiv
