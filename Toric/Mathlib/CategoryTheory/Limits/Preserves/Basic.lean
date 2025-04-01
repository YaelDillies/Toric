import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Toric.Mathlib.CategoryTheory.Limits.Shapes.WithFinalObject

open CategoryTheory

namespace CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

instance PreservesLimitsOfShape.overPost {X : C} {F : C ⥤ D}
  [PreservesLimitsOfShape (WithFinalObject J) F] :
    PreservesLimitsOfShape J (Over.post F (X := X)) where
    preservesLimit {K} := {
      preserves {lim} h := by
        apply Nonempty.intro
        let lim_C := WithFinalObject.coneToOver lim
        have is_limit_forget := WithFinalObject.limit_of_Over _ h
        have : Nonempty (IsLimit (F.mapCone lim_C)) :=
          PreservesLimitsOfShape.preservesLimit.preserves is_limit_forget
        have is_lim_D : IsLimit (F.mapCone lim_C) := Classical.choice this

        have is_lim_D := Equiv.invFun
         (IsLimit.postcomposeHomEquiv (WithFinalObject.extendCompose K F)
          (F.mapCone lim_C)) is_lim_D

        let same_cone_in_D := ((Cones.postcompose (WithFinalObject.extendCompose K F).hom).obj
         (F.mapCone lim_C))

        have cone_iso : same_cone_in_D ≅ WithFinalObject.coneToOver ((Over.post F).mapCone lim) :=
         Cones.ext (Iso.refl same_cone_in_D.pt) (fun a => match a with
          | none => by aesop
          | some a => by aesop)

        have is_lim_D : IsLimit (WithFinalObject.coneToOver ((Over.post F).mapCone lim)) :=
          is_lim_D.ofIsoLimit cone_iso

        have is_lim_over_D := WithFinalObject.limit_forget _ is_lim_D

        exact IsLimit.ofIsoLimit is_lim_over_D
          (WithFinalObject.coneToFrom ((Over.post F).mapCone lim))
    }

instance PreservesFiniteLimits.overPost {X : C} {F : C ⥤ D}
(h : ∀ (J :Type w) [SmallCategory J] [FinCategory J] , PreservesLimitsOfShape J F)
[SmallCategory J] [FinCategory J] :  PreservesLimitsOfShape J (Over.post F (X := X)) :=
by infer_instance


instance PreservesLimitsOfShape.overPostEquivFunctor {X : C} {F : C ≌ D}
    [PreservesLimitsOfShape J F.functor] :
    PreservesLimitsOfShape J (Over.postEquiv F (X := X)).functor := sorry

instance PreservesLimitsOfShape.overPostEquivInverse {X : C} {F : C ≌ D}
    [PreservesLimitsOfShape J F.inverse] :
    PreservesLimitsOfShape J (Over.postEquiv F (X := X)).inverse := sorry

instance PreservesLimitsOfSize.overPost {X : C} {F : C ⥤ D} [PreservesLimitsOfSize.{w', w} F] :
    PreservesLimitsOfSize.{w', w} (Over.post F (X := X)) where
  preservesLimitsOfShape := inferInstance

instance PreservesLimitsOfSize.overPostEquivFunctor {X : C} {F : C ≌ D}
    [PreservesLimitsOfSize.{w', w} F.functor] :
    PreservesLimitsOfSize.{w', w} (Over.postEquiv F (X := X)).functor where
  preservesLimitsOfShape := inferInstance

instance PreservesLimitsOfSize.overPostEquivInverse {X : C} {F : C ≌ D}
    [PreservesLimitsOfSize.{w', w} F.inverse] :
    PreservesLimitsOfSize.{w', w} (Over.postEquiv F (X := X)).inverse where
  preservesLimitsOfShape := inferInstance

end CategoryTheory.Limits
