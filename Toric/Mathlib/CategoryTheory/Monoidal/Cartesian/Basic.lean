import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

namespace CategoryTheory.CartesianMonoidalCategory
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}

open MonoidalCategory

@[reassoc (attr := simp)]
lemma tensorμ_fst (W X Y Z : C) : tensorμ W X Y Z ≫ fst (W ⊗ Y) (X ⊗ Z) = fst W X ⊗ₘ fst Y Z := by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
lemma tensorμ_snd (W X Y Z : C) : tensorμ W X Y Z ≫ snd (W ⊗ Y) (X ⊗ Z) = snd W X ⊗ₘ snd Y Z := by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
lemma tensorδ_fst (W X Y Z : C) : tensorδ W X Y Z ≫ fst (W ⊗ X) (Y ⊗ Z) = fst W Y ⊗ₘ fst X Z := by
  ext <;> simp [tensorδ]

@[reassoc (attr := simp)]
lemma tensorδ_snd (W X Y Z : C) : tensorδ W X Y Z ≫ snd (W ⊗ X) (Y ⊗ Z) = snd W Y ⊗ₘ snd X Z := by
  ext <;> simp [tensorδ]

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

namespace CategoryTheory.CartesianMonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {D E : Type*} [Category D] [Category E] [CartesianMonoidalCategory E]

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory

attribute [ext] toUnit_unique

@[simps]
def homToProd {X Y Z : C} : (Z ⟶ X ⊗ Y) ≃ (Z ⟶ X) × (Z ⟶ Y) where
  toFun f := ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  invFun f := lift f.1 f.2
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] lemma toUnit_unit : toUnit (𝟙_ C) = 𝟙 (𝟙_ C) := toUnit_unique ..

end CategoryTheory.CartesianMonoidalCategory
