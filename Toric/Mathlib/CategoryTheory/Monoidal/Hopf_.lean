import Mathlib.CategoryTheory.Monoidal.Hopf_
import Toric.Mathlib.CategoryTheory.Monoidal.Bimon_

/-!
# TODO

Make `antipode_left`/`antipode_right` auto-param to `aesop_cat`?
-/

assert_not_exists CategoryTheory.ChosenFiniteProducts

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

section HopfOp
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

def hopfOpEquiv : Hopf_ Cᵒᵖ ≅ (Hopf_ C)ᵒᵖ := sorry

end HopfOp

namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]

-- /-- A monoidal functor takes Hopf objects to Hopf objects.

-- That is, a monoidal functor `F : C ⥤ D` induces a functor `Hopf_ C ⥤ Hopf_ D`. -/
-- @[simps!]
-- def mapHopf (F : C ⥤ D) [F.Monoidal] : Hopf_ C ⥤ Hopf_ D where
--   obj H := {
--     X := F.mapBimon.obj H.X
--     antipode := F.map H.antipode
--     antipode_left := sorry
--     antipode_right := sorry
--   }
--   map f := F.mapBimon.map f
--   map_id _ := F.mapBimon.map_id _
--   map_comp := F.mapBimon.map_comp

end CategoryTheory.Functor
