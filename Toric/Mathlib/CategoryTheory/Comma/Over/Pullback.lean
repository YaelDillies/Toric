import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Toric.Mathlib.CategoryTheory.Comma.Over.Basic

namespace CategoryTheory.Over

open Limits

universe v
variable {C : Type*} [Category.{v} C] [HasPullbacks C] {X Y : C} {f : X ⟶ Y}

/-- The pullback along an epi that's preserved under pullbacks is faithful.

This "preserved under" pullbacks" condition is automatically satisfied in abelian categories:
```
example [Abelian C] [Epi f] : (pullback f).Faithful := inferInstance
```
-/
instance faithful_pullback [∀ Z (g : Z ⟶ Y), Epi (pullback.fst g f)] : (pullback f).Faithful := by
  have (Z : Over Y) : Epi ((mapPullbackAdj f).counit.app Z) := by simp; infer_instance
  exact (mapPullbackAdj f).faithful_R_of_epi_counit_app

end CategoryTheory.Over
