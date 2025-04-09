import Mathlib.CategoryTheory.Monoidal.Functor

universe v₁ v₂ v₃ v₁' u₁ u₂ u₃ u₁'

namespace CategoryTheory

open Category Functor MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]
  {C' : Type u₁'} [Category.{v₁'} C']

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.Monoidal] [adj.IsMonoidal]

open Functor.OplaxMonoidal Functor.LaxMonoidal

@[reassoc]
lemma ε_comp_map_ε : ε G ≫ G.map (ε F) = adj.unit.app (𝟙_ C) := by
  simp [← adj.unit_app_unit_comp_map_η]

attribute [simp] map_ε_comp_counit_app_unit map_ε_comp_counit_app_unit_assoc

end Adjunction

namespace Equivalence
variable {e : C ≌ D} [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]

open Functor.OplaxMonoidal Functor.LaxMonoidal

@[reassoc]
lemma unit_app_comp_inverse_map_η_functor :
    e.unit.app (𝟙_ C) ≫ e.inverse.map (η e.functor) = ε e.inverse :=
  e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]
lemma unit_app_tensor_comp_inverse_map_δ_functor (X Y : C) :
    e.unit.app (X ⊗ Y) ≫ e.inverse.map (δ e.functor X Y) =
      (e.unit.app X ⊗ e.unitIso.hom.app Y) ≫ μ e.inverse _ _ :=
  e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc (attr := simp)]
lemma functor_map_ε_inverse_comp_counit_app :
    e.functor.map (ε e.inverse) ≫ e.counit.app (𝟙_ D) = η e.functor :=
  e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]
lemma functor_map_μ_inverse_comp_counit_app_tensor (X Y : D) :
    e.functor.map (μ e.inverse X Y) ≫ e.counit.app (X ⊗ Y) =
      δ e.functor _ _ ≫ (e.counit.app X ⊗ e.counit.app Y) :=
  e.toAdjunction.map_μ_comp_counit_app_tensor X Y

@[reassoc]
lemma counitInv_app_comp_functor_map_η_inverse :
    e.counitInv.app (𝟙_ D) ≫ e.functor.map (η e.inverse) = ε e.functor := by
  rw [← cancel_epi (η e.functor), Monoidal.η_ε, ← functor_map_ε_inverse_comp_counitIso_hom_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, Monoidal.map_ε_η]

@[reassoc]
lemma counitInv_app_tensor_comp_functor_map_δ_inverse (X Y : C) :
    e.counitInv.app (e.functor.obj X ⊗ e.functor.obj Y) ≫
      e.functor.map (δ e.inverse (e.functor.obj X) (e.functor.obj Y)) =
      μ e.functor X Y ≫ e.functor.map (e.unitIso.hom.app X ⊗ e.unitIso.hom.app Y) := by
  rw [← cancel_epi (δ e.functor _ _), Monoidal.δ_μ_assoc]
  apply e.inverse.map_injective
  simp [← cancel_epi (e.unitIso.hom.app (X ⊗ Y)), Functor.map_comp,
    unitIso_hom_app_tensor_comp_inverse_map_δ_functor_assoc]

@[reassoc (attr := simp)]
lemma ε_comp_map_ε : ε e.inverse ≫ e.inverse.map (ε e.functor) = e.unit.app (𝟙_ C) :=
  e.toAdjunction.ε_comp_map_ε

end Equivalence
end CategoryTheory
