import Mathlib.CategoryTheory.Comma.Over.Basic

namespace CategoryTheory
universe v₁ v₂ u₁ u₂
variable {T : Type u₁} [Category.{v₁, u₁} T] {D : Type u₂} [Category.{v₂, u₂} D]

-- TODO: Replace
abbrev Functor.FullyFaithful.over {X : T} {F : T ⥤ D} (h : F.FullyFaithful) :
    (Over.post F (X := X)).FullyFaithful := Over.FullyFaithful.over _ _ h

end CategoryTheory

namespace CategoryTheory.Over

open Limits

/-- If `X : C` is initial, then the under category of `X` is equivalent to `C`. -/
@[simps]
def equivalenceOfIsTerminal {C : Type*} [Category C] {X : C} (hX : IsTerminal X) : Over X ≌ C where
  functor := forget X
  inverse := { obj Y := mk (hX.from Y), map f := homMk f }
  unitIso := NatIso.ofComponents (fun Y ↦ isoMk (.refl _) (hX.hom_ext _ _))
  counitIso := NatIso.ofComponents (fun _ ↦ .refl _)

end CategoryTheory.Over
