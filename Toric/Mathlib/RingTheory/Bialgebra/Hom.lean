import Mathlib.RingTheory.Bialgebra.Hom

open Function

namespace BialgHom
variable {F R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] [FunLike F A B]
  [BialgHomClass F R A B]

lemma toAlgHom_injective : Injective ((↑) : (A →ₐc[R] B) → A →ₐ[R] B) :=
  fun _f _g hfg ↦ DFunLike.coe_injective congr($hfg)

end BialgHom

@[simp]
lemma BialgHom.toLinearMap_apply {R A B : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]
    [Semiring B] [Bialgebra R B] (f : A →ₐc[R] B) (x : A) : f.toLinearMap x = f x := rfl

namespace BialgHom

open Bialgebra Coalgebra Algebra.TensorProduct

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B]

@[simps!]
def ofAlgHom' (f : A →ₐ[R] B) (counit_comp : (counitAlgHom R B).comp f = (counitAlgHom R A))
    (map_comp_comul : (map f f).comp (comulAlgHom _ _) = (comulAlgHom _ _).comp f) :
    A →ₐc[R] B := .ofAlgHom f congr(($counit_comp).toLinearMap) congr(($map_comp_comul).toLinearMap)

end BialgHom
