/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory Mon_Class MonoidalCategory

namespace Mon_

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {M N : Mon_ C}
variable {S : C}

/--
An action of a monoid object `M` on an object `S` is the data of map
`smul : M ⊗ S ⟶ S` that satisfies "the right commutative diagrams":
-/
class Action where
  smul : M.X ⊗ S ⟶ S
  mul_smul : (𝟙 M.X ⊗ smul) ≫ smul
    = (α_ M.X M.X S).inv ≫ (M.mul ⊗ (𝟙 S)) ≫ smul
  one_smul : (λ_ S).inv ≫ M.one ▷ S ≫ smul = 𝟙 S

end Mon_
