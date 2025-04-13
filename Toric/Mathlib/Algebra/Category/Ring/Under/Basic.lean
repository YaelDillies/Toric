import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Toric.Mathlib.CategoryTheory.Limits.Constructions.Over.Products

open CategoryTheory Limits Opposite

namespace CommRingCat.Under
variable {R : CommRingCat}

/-- A choice of finite products of `(Under R)ᵒᵖ` for `R : CommRingCat` given by the tensor product.
-/
noncomputable instance chosenFiniteProducts : ChosenFiniteProducts (Under R)ᵒᵖ where
  product X Y := {
    cone := BinaryCofan.op <| pushoutCoconeEquivBinaryCofan.functor.obj <|
      pushoutCocone R (unop X).right (unop Y).right
    isLimit := BinaryCofan.IsColimit.op
      (CommRingCat.pushoutCoconeIsColimit R _ _).pushoutCoconeEquivBinaryCofan
  }
  terminal := ⟨_, terminalOpOfInitial Under.mkIdInitial⟩

end CommRingCat.Under
