import Mathlib.CategoryTheory.ChosenFiniteProducts

/-!
# This is https://github.com/leanprover-community/mathlib4/pull/22168
-/

namespace CategoryTheory

universe v v₁ v₂ u u₁ u₂

open ChosenFiniteProducts

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]

open MonoidalCategory

@[reassoc (attr := simp)]
theorem comp_toUnit {X Y : C} (f : X ⟶ Y) : f ≫ toUnit Y = toUnit X :=
  toUnit_unique _ _

theorem lift_snd_fst {X Y : C} : lift (snd X Y) (fst X Y) = (β_ X Y).hom := rfl

end CategoryTheory
