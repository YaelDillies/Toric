import Mathlib.CategoryTheory.Comma.Over.Pullback
import Toric.Mathlib.CategoryTheory.Comma.Over.Basic

namespace CategoryTheory.Over

open Limits

/-- If `X : C` is initial, then the under category of `X` is equivalent to `C`. -/
@[simps!]
noncomputable def forgetMapTerminal {C : Type*} [Category C] [HasTerminal C] (S : C) :
    forget _ ≅ map (terminal.from S) ⋙ (equivalenceOfIsTerminal terminalIsTerminal).functor :=
  NatIso.ofComponents (fun X ↦ .refl _) (by simp)

instance {C : Type*} [Category C] [HasBinaryProducts C] {X : C} : (Over.star X).IsRightAdjoint :=
  ⟨_, ⟨forgetAdjStar X⟩⟩

end CategoryTheory.Over
