/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Toric.Torus

/-!
# Toric varieties

This file defines a toric variety over a ring `R` as a scheme `X` with a structure morphism to
`Spec R`.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry
variable {R : CommRingCat} {n : ℕ}

variable (R n)
/-- A toric variety of dimension `n` over a ring `R` is a scheme `X` equipped with a dense embedding
`Tⁿ → X` and an action `T × X → X` extending the standard action `T × T → T`. -/
class ToricVariety (X : Scheme) extends X.Over (Spec R) where
  /-- The torus action on a toric variety. -/
  torusAct : pullback (Torus R n ↘ Spec R) (X ↘ Spec R) ⟶ X
  -- exists_isOpen_orbit : ∃ a : X, IsOpen (.range (torusAct.base sorry))
