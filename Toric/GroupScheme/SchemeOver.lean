/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Toric.Mathlib.CategoryTheory.ChosenFiniteProducts.Over

/-!
# Schemes over a scheme

This file proves that schemes over a fixed scheme form a monoidal category.
-/

open CategoryTheory
open scoped MonoidalCategory

namespace AlgebraicGeometry
variable {R : CommRingCat} {S X Y Z : Scheme}

noncomputable instance : ChosenFiniteProducts (Over S) := Over.chosenFiniteProducts _

lemma tensorUnit_def : 𝟙_ (Over S) = .mk (𝟙 S) := rfl

end AlgebraicGeometry
