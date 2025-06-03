import Mathlib.CategoryTheory.Monoidal.Category

namespace CategoryTheory.Monoidal
variable {C : Type*} [Category C] [MonoidalCategory C]

open scoped MonoidalCategory

lemma id_tensorHom_id (X Y : C) : 𝟙 X ⊗ 𝟙 Y = 𝟙 (X ⊗ Y) := by simp

end CategoryTheory.Monoidal
