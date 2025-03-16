import Mathlib.CategoryTheory.Limits.Preserves.Finite

namespace CategoryTheory.Limits

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

instance PreservesFiniteProducts.overPost {X : C} {F : C ⥤ D} [PreservesFiniteProducts F] :
    PreservesFiniteProducts (Over.post F (X := X)) := sorry

end CategoryTheory.Limits
