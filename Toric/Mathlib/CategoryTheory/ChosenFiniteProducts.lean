import Mathlib.CategoryTheory.ChosenFiniteProducts

namespace CategoryTheory

universe v v₁ v₂ u u₁ u₂

namespace ChosenFiniteProducts

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]

open MonoidalCategory

@[simp]
lemma lift_snd_comp_fst_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (snd _ _ ≫ g') (fst _ _ ≫ g) = (β_ _ _).hom ≫ (g' ⊗ g) := by ext <;> simp

end ChosenFiniteProducts

end CategoryTheory
