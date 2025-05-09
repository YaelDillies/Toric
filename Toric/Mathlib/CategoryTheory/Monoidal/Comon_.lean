import Mathlib.CategoryTheory.Monoidal.Comon_
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.CategoryTheory.Opposites

open CategoryTheory

universe u₁ v₁ u₂ v₂
variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

instance : (opOpEquivalence C).functor.LaxMonoidal := sorry
instance : (opOpEquivalence C).inverse.LaxMonoidal := sorry

@[simps!]
def monOpEquivComonOp : Mon_ Cᵒᵖ ≌ (Comon_ C)ᵒᵖ := (Comon_.Comon_EquivMon_OpOp C).symm.rightOp

-- @[simps!]
def comonOpEquivMonOp : Comon_ Cᵒᵖ ≌ (Mon_ C)ᵒᵖ :=
  sorry
  -- (Comon_.Comon_EquivMon_OpOp Cᵒᵖ).trans <| .op (opOpEquivalence C).mapMon

variable [BraidedCategory C]

instance : (monOpEquivComonOp C).functor.OplaxMonoidal := sorry
instance : (monOpEquivComonOp C).inverse.OplaxMonoidal := sorry

namespace CategoryTheory.Equivalence
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

def mapComon (e : C ≌ D) [e.functor.OplaxMonoidal] [e.inverse.OplaxMonoidal] :
    Comon_ C ≌ Comon_ D where
  functor := e.functor.mapComon
  inverse := e.inverse.mapComon
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

end CategoryTheory.Equivalence
