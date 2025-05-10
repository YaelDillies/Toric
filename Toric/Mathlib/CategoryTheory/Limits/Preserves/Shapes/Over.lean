import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.WithTerminal.FinCategory
import Mathlib.CategoryTheory.WithTerminal.Cone

namespace CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J] {X : C} {F : C ⥤ D}

open WithTerminal in
instance PreservesLimitsOfShape.overPost
    [PreservesLimitsOfShape (WithTerminal J) F] :
    PreservesLimitsOfShape J (Over.post F (X := X)) where
  preservesLimit {K} := {
    preserves {coneK} isLimitConeK := by
      let coneC := coneEquiv.functor.obj coneK
      obtain ⟨isLimitConeD⟩ : Nonempty (IsLimit (F.mapCone coneC)) :=
        PreservesLimitsOfShape.preservesLimit.preserves <| isLimitEquiv.symm isLimitConeK
      replace isLimitConeD :=
        (IsLimit.postcomposeHomEquiv liftFromOverComp.symm (F.mapCone coneC)).symm isLimitConeD
      exact ⟨isLimitEquiv <| isLimitConeD.ofIsoLimit <|
        Cones.ext (.refl _) fun | .star | .of a => by aesop⟩
  }

instance PreservesFiniteLimits.overPost [PreservesFiniteLimits F] :
    PreservesFiniteLimits (Over.post F (X := X)) where
  preservesFiniteLimits _ := inferInstance

instance PreservesLimitsOfSize.overPost [PreservesLimitsOfSize.{w', w} F] :
    PreservesLimitsOfSize.{w', w} (Over.post F (X := X)) where

open WithInitial in
instance PreservesColimitsOfShape.underPost
    [PreservesColimitsOfShape (WithInitial J) F] :
    PreservesColimitsOfShape J (Under.post F (X := X)) where
  preservesColimit {K} := {
    preserves {coconeK} isLimitCoconeK := by
      let coconeC := coconeEquiv.functor.obj coconeK
      obtain ⟨isColimitCoconeD⟩ : Nonempty (IsColimit (F.mapCocone coconeC)) :=
        PreservesColimitsOfShape.preservesColimit.preserves <| isColimitEquiv.symm isLimitCoconeK
      replace isColimitCoconeD :=
        (IsColimit.precomposeHomEquiv liftFromUnderComp (F.mapCocone coconeC)).symm isColimitCoconeD
      exact ⟨isColimitEquiv <| isColimitCoconeD.ofIsoColimit <|
        Cocones.ext (.refl _) fun | .star | .of a => by aesop⟩
  }

instance PreservesFiniteColimits.underPost [PreservesFiniteColimits F] :
    PreservesFiniteColimits (Under.post F (X := X)) where
  preservesFiniteColimits _ := inferInstance

instance PreservesColimitsOfSize.underPost [PreservesColimitsOfSize.{w', w} F] :
    PreservesColimitsOfSize.{w', w} (Under.post F (X := X)) where

end CategoryTheory.Limits
