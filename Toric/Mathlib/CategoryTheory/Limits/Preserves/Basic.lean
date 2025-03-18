import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic

namespace CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

instance PreservesLimitsOfShape.overPost {X : C} {F : C ⥤ D} [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J (Over.post F (X := X)) := sorry

instance PreservesLimitsOfShape.overPostEquivFunctor {X : C} {F : C ≌ D}
    [PreservesLimitsOfShape J F.functor] :
    PreservesLimitsOfShape J (Over.postEquiv F (X := X)).functor := .overPost

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
