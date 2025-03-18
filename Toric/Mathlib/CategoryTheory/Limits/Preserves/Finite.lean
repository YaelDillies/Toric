import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Toric.Mathlib.CategoryTheory.Limits.Preserves.Basic

namespace CategoryTheory.Limits

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

instance PreservesFiniteProducts.overPost {X : C} {F : C ⥤ D} [PreservesFiniteProducts F] :
    PreservesFiniteProducts (Over.post F (X := X)) where preserves _ := inferInstance

instance PreservesFiniteProducts.overPostEquivFunctor {X : C} {F : C ≌ D}
    [PreservesFiniteProducts F.functor] :
    PreservesFiniteProducts (Over.postEquiv F (X := X)).functor where preserves _ := inferInstance

instance PreservesFiniteProducts.overPostEquivInverse {X : C} {F : C ≌ D}
    [PreservesFiniteProducts F.inverse] :
    PreservesFiniteProducts (Over.postEquiv F (X := X)).inverse where preserves _ := inferInstance

end CategoryTheory.Limits
