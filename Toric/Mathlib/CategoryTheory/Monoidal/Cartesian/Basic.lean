import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

namespace CategoryTheory.CartesianMonoidalCategory
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}

open MonoidalCategory

@[reassoc (attr := simp)]
lemma lift_tensorHom_tensorHom (f₁ : X₁ ⟶ Y₁) (g₁ : X₁ ⟶ Z₁) (f₂ : X₂ ⟶ Y₂) (g₂ : X₂ ⟶ Z₂) :
    lift (f₁ ⊗ₘ f₂) (g₁ ⊗ₘ g₂) = (lift f₁ g₁ ⊗ₘ lift f₂ g₂) ≫ tensorδ Y₁ Y₂ Z₁ Z₂ := by
  ext <;> simp [tensorδ]

@[reassoc (attr := simp)]
lemma lift_tensorHom_id (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    lift (f₁ ⊗ₘ f₂) (𝟙 (X₁ ⊗ X₂)) = (lift f₁ (𝟙 X₁) ⊗ₘ lift f₂ (𝟙 X₂)) ≫ tensorδ Y₁ Y₂ X₁ X₂ := by
  ext <;> simp [tensorδ]

@[reassoc (attr := simp)]
lemma lift_id_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    lift (𝟙 (X₁ ⊗ X₂)) (f₁ ⊗ₘ f₂) = (lift (𝟙 X₁) f₁ ⊗ₘ lift (𝟙 X₂) f₂) ≫ tensorδ X₁ X₂ Y₁ Y₂ := by
  ext <;> simp [tensorδ]

end CategoryTheory.CartesianMonoidalCategory
