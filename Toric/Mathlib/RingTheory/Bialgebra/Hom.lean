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
