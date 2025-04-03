import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Toric.Mathlib.CategoryTheory.WithTerminal.Cones

open CategoryTheory

namespace CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

instance PreservesLimitsOfShape.overPost {X : C} {F : C ⥤ D}
  [PreservesLimitsOfShape (WithTerminal J) F] :
    PreservesLimitsOfShape J (Over.post F (X := X)) where
    preservesLimit {K} := {
      preserves {lim} h := by
        apply Nonempty.intro
        let lim_C := WithTerminal.coneLift.obj lim
        have is_limit_forget := WithTerminal.limitEquiv.symm h
        have : Nonempty (IsLimit (F.mapCone lim_C)) :=
          PreservesLimitsOfShape.preservesLimit.preserves is_limit_forget
        have is_lim_D : IsLimit (F.mapCone lim_C) := Classical.choice this

        have is_lim_D := (IsLimit.postcomposeHomEquiv (WithTerminal.extendCompose K F)
          (F.mapCone lim_C)).symm is_lim_D

        let same_cone_in_D := (Cones.postcompose (WithTerminal.extendCompose K F).hom).obj
         (F.mapCone lim_C)

        have cone_iso : same_cone_in_D ≅ WithTerminal.coneLift.obj ((Over.post F).mapCone lim) :=
         Cones.ext (Iso.refl same_cone_in_D.pt) (fun
          | .star => by aesop
          | .of a => by aesop)

        exact WithTerminal.limitEquiv.toFun (is_lim_D.ofIsoLimit cone_iso)
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
