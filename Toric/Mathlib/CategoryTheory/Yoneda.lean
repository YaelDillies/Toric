import Mathlib.CategoryTheory.Yoneda

open Opposite

namespace CategoryTheory
variable {C : Type*} [Category C]

def opOpYoneda : yoneda ⋙ (whiskeringLeft _ _ _).obj (opOp C) ≅ coyoneda :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ (opEquiv (op Y) X).toIso)
    (fun _ ↦ rfl)) (fun _ ↦ rfl)

end CategoryTheory
