import Mathlib.CategoryTheory.Comma.Over.Basic

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
