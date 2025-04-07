import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Toric.Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

open CategoryTheory Limits Opposite

namespace CommRingCat.Under
variable {R : CommRingCat}

/-- A choice of finite products of `(Under R)ᵒᵖ` for `R : CommRingCat` given by the tensor product.
-/
noncomputable instance chosenFiniteProducts : ChosenFiniteProducts (Under R)ᵒᵖ where
  product X Y := {
    cone := BinaryCofan.op <| pushoutCocone.toBinaryCofan.obj <|
      pushoutCocone R (unop X).right (unop Y).right
    isLimit := BinaryCofan.IsColimit.op <| pushoutCocone.IsColimit.toBinaryCofanIsColimit <|
        CommRingCat.pushoutCoconeIsColimit R _ _
  }
  terminal := ⟨_, terminalOpOfInitial Under.mkIdInitial⟩

instance : PreservesFiniteProducts (Under.opToOverOp R) := sorry

end CommRingCat.Under
