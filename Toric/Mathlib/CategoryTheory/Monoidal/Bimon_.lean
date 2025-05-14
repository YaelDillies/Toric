import Mathlib.CategoryTheory.Monoidal.Bimon_
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.Comon_

open CategoryTheory MonoidalCategory Opposite

universe v₁ v₂ u₁ u₂ u
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

-- def bimonOpEquiv : Bimon_ Cᵒᵖ ≌ (Bimon_ C)ᵒᵖ :=
--   .trans (D := Comon_ (Comon_ C)ᵒᵖ)
--   -- `Bimon_ Cᵒᵖ ≌ Comon_ (Comon_ C)ᵒᵖ`
--   (monOpEquivComonOp _).mapComon <| .trans (D := (Mon_ (Comon_ C))ᵒᵖ)
--   -- `Comon_ (Comon_ C)ᵒᵖ ≌ (Mon_ (Comon_ C))ᵒᵖ`
--   (comonOpEquivMonOp _) <|
--   -- `(Mon_ (Comon_ C))ᵒᵖ ≌ (Bimon_ C)ᵒᵖ`
--   (Bimon_.equivMon_Comon_ C).symm.op

namespace CategoryTheory.Functor
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]

-- /-- A monoidal functor takes bimonoid objects to bimonoid objects.

-- That is, a monoidal functor `F : C ⥤ D` induces a functor `Bimon_ C ⥤ Bimon_ D`.

-- Michał thinks the current construction might not work. -/
-- @[simps!] def mapBimon (F : C ⥤ D) [F.Monoidal] : Bimon_ C ⥤ Bimon_ D := F.mapMon.mapComon

end CategoryTheory.Functor
