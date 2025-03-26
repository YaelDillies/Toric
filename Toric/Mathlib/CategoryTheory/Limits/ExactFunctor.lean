import Mathlib.CategoryTheory.Limits.ExactFunctor

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Limits

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

def LeftExactFunctor.fullyFaithful : (LeftExactFunctor.forget C D).FullyFaithful :=
  fullyFaithfulFullSubcategoryInclusion _

end CategoryTheory
