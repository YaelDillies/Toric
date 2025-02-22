import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

@[simp]
lemma pullback.lift_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    lift (fst f g) (snd f g) condition = 𝟙 (pullback f g) := by
  apply hom_ext <;> simp

end CategoryTheory.Limits
