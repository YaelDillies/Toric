import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
### TODO

Protect `ClosedUnderLimitsOfShape.limit`
-/

namespace CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w w'
variable {J : Type w} [Category.{w'} J]
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D)

/-- The essential image of a functor is closed under the limits it preserves. -/
protected lemma ClosedUnderLimitsOfShape.essImage [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] [F.Full] [F.Faithful] : ClosedUnderLimitsOfShape J F.essImage := by
  rintro G c hc hG
  choose Hobj e using hG
  replace e i := (e i).some
  have hF : F.FullyFaithful := .ofFullyFaithful _
  let H : J ⥤ C := {
    obj := Hobj
    map {i j} f := hF.preimage <| (e i).hom ≫ G.map f ≫ (e j).inv
    map_id i := F.map_injective <| by simp
    map_comp {i j k} f g := F.map_injective <| by simp
  }
  exact ⟨Limits.limit H, ⟨IsLimit.conePointsIsoOfNatIso (s := F.mapCone <| limit.cone H)
    (isLimitOfPreserves _ (limit.isLimit H)) hc <| NatIso.ofComponents e⟩⟩

end CategoryTheory.Limits
