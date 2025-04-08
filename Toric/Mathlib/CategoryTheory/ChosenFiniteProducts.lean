import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

open Limits ChosenFiniteProducts

namespace Functor

open LaxMonoidal Monoidal

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]
  {D : Type u₁} [Category.{v₁} D] [ChosenFiniteProducts D]
  {E : Type u₃} [Category.{v₃} E] [ChosenFiniteProducts E]
  (F : C ⥤ D) [PreservesFiniteProducts F]
  (G : D ⥤ E) [PreservesFiniteProducts G]

attribute [local instance] monoidalOfChosenFiniteProducts

attribute [instance] NatTrans.monoidal_of_preservesFiniteProducts

lemma ε_of_chosenFiniteProducts : ε F = (preservesTerminalIso F).inv := by
  change (εIso F).symm.inv = _; congr; ext; simp; rfl

lemma μ_of_chosenFiniteProducts (X Y : C) : μ F X Y = (prodComparisonIso F X Y).inv := by
  change (μIso F X Y).symm.inv = _; congr; ext : 1; rfl

@[simp]
lemma preservesTerminalIso_id : preservesTerminalIso (𝟭 C) = .refl _ := by
  ext; exact toUnit_unique ..

@[simp]
lemma preservesTerminalIso_comp :
    preservesTerminalIso (F ⋙ G) =
      G.mapIso (preservesTerminalIso F) ≪≫ preservesTerminalIso G := by
  ext; exact toUnit_unique ..

@[simp]
lemma prodComparisonIso_id (X Y : C) : prodComparisonIso (𝟭 C) X Y = .refl _ := by
  ext <;> simp

@[simp]
lemma prodComparisonIso_comp (X Y : C) :
    prodComparisonIso (F ⋙ G) X Y =
      G.mapIso (prodComparisonIso F X Y) ≪≫ prodComparisonIso G (F.obj X) (F.obj Y) := by
  ext <;> simp [ChosenFiniteProducts.prodComparison, ← G.map_comp]

-- TODO: Rename
alias map_toUnit_comp_terminalComparison := map_toUnit_comp_terminalCompariso

end CategoryTheory.Functor
