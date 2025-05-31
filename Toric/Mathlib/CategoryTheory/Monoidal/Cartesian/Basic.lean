import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

namespace CategoryTheory.CartesianMonoidalCategory
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

open MonoidalCategory

@[reassoc (attr := simp)]
lemma tensorμ_comp_fst (W X Y Z : C) :
    tensorμ W X Y Z ≫ fst (W ⊗ Y) (X ⊗ Z) = fst W X ⊗ fst Y Z := by ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
lemma tensorμ_comp_snd (W X Y Z : C) :
    tensorμ W X Y Z ≫ snd (W ⊗ Y) (X ⊗ Z) = snd W X ⊗ snd Y Z := by ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
lemma tensorδ_comp_fst (W X Y Z : C) :
    tensorδ W X Y Z ≫ fst (W ⊗ X) (Y ⊗ Z) = fst W Y ⊗ fst X Z := by ext <;> simp [tensorδ]

@[reassoc (attr := simp)]
lemma tensorδ_comp_snd (W X Y Z : C) :
    tensorδ W X Y Z ≫ snd (W ⊗ X) (Y ⊗ Z) = snd W Y ⊗ snd X Z := by ext <;> simp [tensorδ]

end CategoryTheory.CartesianMonoidalCategory
