import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

namespace CategoryTheory.CartesianMonoidalCategory
variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

open MonoidalCategory

@[reassoc (attr := simp)] lemma rightUnitor_tensorUnit_hom_leftUnitor_tensorUnit_inv :
    (ρ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv = 𝟙 (𝟙_ C ⊗ 𝟙_ C) := by
   simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]

@[reassoc (attr := simp)] lemma leftUnitor_tensorUnit_hom_rightUnitor_tensorUnit_inv :
    (λ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv = 𝟙 (𝟙_ C ⊗ 𝟙_ C) := by
   simp [toUnit_unique (λ_ (𝟙_ C)).hom (ρ_ (𝟙_ C)).hom]

@[reassoc (attr := simp)] lemma leftUnitor_tensorUnit_inv_rightUnitor_tensorUnit_hom :
    (λ_ (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
   simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]

@[reassoc (attr := simp)] lemma rightUnitor_tensorUnit_inv_leftUnitor_tensorUnit_hom :
    (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
   simp [toUnit_unique (λ_ (𝟙_ C)).hom (ρ_ (𝟙_ C)).hom]

variable [BraidedCategory C] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}

@[reassoc (attr := simp)]
lemma tensorμ_fst (W X Y Z : C) : tensorμ W X Y Z ≫ fst (W ⊗ Y) (X ⊗ Z) = fst W X ⊗ fst Y Z := by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
lemma tensorμ_snd (W X Y Z : C) : tensorμ W X Y Z ≫ snd (W ⊗ Y) (X ⊗ Z) = snd W X ⊗ snd Y Z := by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
lemma tensorδ_fst (W X Y Z : C) : tensorδ W X Y Z ≫ fst (W ⊗ X) (Y ⊗ Z) = fst W Y ⊗ fst X Z := by
  ext <;> simp [tensorδ]

@[reassoc (attr := simp)]
lemma tensorδ_snd (W X Y Z : C) : tensorδ W X Y Z ≫ snd (W ⊗ X) (Y ⊗ Z) = snd W Y ⊗ snd X Z := by
  ext <;> simp [tensorδ]

@[reassoc (attr := simp)]
lemma lift_tensorHom_tensorHom (f₁ : X₁ ⟶ Y₁) (g₁ : X₁ ⟶ Z₁) (f₂ : X₂ ⟶ Y₂) (g₂ : X₂ ⟶ Z₂) :
    lift (f₁ ⊗ f₂) (g₁ ⊗ g₂) = (lift f₁ g₁ ⊗ lift f₂ g₂) ≫ tensorδ Y₁ Y₂ Z₁ Z₂ := by
  ext <;> simp [tensorδ]

end CategoryTheory.CartesianMonoidalCategory
