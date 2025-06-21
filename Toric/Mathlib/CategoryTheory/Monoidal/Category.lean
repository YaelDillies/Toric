import Mathlib.CategoryTheory.Monoidal.Category

namespace CategoryTheory.Monoidal
variable {C : Type*} [Category C] [MonoidalCategory C] {X Y Z : C}

open MonoidalCategory

-- TODO: Rename
lemma id_tensorHom_id (X Y : C) : 𝟙 X ⊗ₘ 𝟙 Y = 𝟙 (X ⊗ Y) := by simp

@[reassoc (attr := simp)]
lemma leftUnitor_comp_tensorHom (f : 𝟙_ C ⟶ Y) (g : X ⟶ Z) :
    (λ_ X).inv ≫ (f ⊗ₘ g) = g ≫ (λ_ Z).inv ≫ f ▷ Z := by
  simp [tensorHom_def']

@[reassoc (attr := simp)]
lemma rightUnitor_comp_tensorHom (f : X ⟶ Y) (g : 𝟙_ C ⟶ Z) :
    (ρ_ X).inv ≫ (f ⊗ₘ g) = f ≫ (ρ_ Y).inv ≫ Y ◁ g := by
  simp [tensorHom_def]

end CategoryTheory.Monoidal
