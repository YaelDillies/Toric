import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Toric.Mathlib.CategoryTheory.Monoidal.Functor

namespace CategoryTheory.Functor
variable {C D : Type*}
  [Category C] [MonoidalCategory C] [BraidedCategory C]
  [Category D] [MonoidalCategory D] [BraidedCategory D]

open MonoidalCategory LaxMonoidal

@[reassoc]
lemma tensorμ_tensorHom_μ_μ_μ (F : C ⥤ D) [F.LaxBraided] (W X Y Z : C) :
    tensorμ (F.obj W) (F.obj X) (F.obj Y) (F.obj Z) ≫
    (μ F W Y ⊗ₘ μ F X Z) ≫ μ F (W ⊗ Y) (X ⊗ Z) = (μ F W X ⊗ₘ μ F Y Z) ≫ μ F (W ⊗ X) (Y ⊗ Z) ≫
      F.map (tensorμ W X Y Z) := by
  rw [tensorHom_def]
  simp only [tensorμ, Category.assoc]
  rw [whiskerLeft_μ_μ,
    associator_inv_naturality_left_assoc, ← pentagon_inv_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc, whiskerRight_μ_μ,
    whiskerLeft_hom_inv_assoc, Iso.inv_hom_id_assoc, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, μ_natural_left_assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← Functor.LaxBraided.braided,
    MonoidalCategory.whiskerLeft_comp_assoc, μ_natural_right, whiskerLeft_μ_μ_assoc,
    comp_whiskerRight_assoc, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, pentagon_inv_assoc, μ_natural_left_assoc, μ_natural_left_assoc,
    Iso.hom_inv_id_assoc, ← associator_inv_naturality_left_assoc, whiskerRight_μ_μ_assoc,
    Iso.inv_hom_id_assoc, ← tensorHom_def_assoc]
  simp only [← map_comp, whisker_assoc, Category.assoc, pentagon_inv_inv_hom_hom_inv,
    pentagon_inv_hom_hom_hom_inv_assoc]

end CategoryTheory.Functor
