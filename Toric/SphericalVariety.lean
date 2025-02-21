/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Toric.Torus

/-!
# Spherical varieties

This file defines a spherical variety over a ring `R` as a scheme `X` with a structure morphism to
`Spec R`.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry
variable {R : CommRingCat} {n : ℕ} {X Y : Scheme}

variable (R n)
/-- A spherical variety of dimension over `B` over a ring `R` is a scheme `X` equipped with an
action `T × B → B` with an open orbit. -/
class SphericalVariety (B X : Scheme) [B.Over (Spec R)] extends X.Over (Spec R) where
  qct : pullback (B ↘ Spec R) (X ↘ Spec R) ⟶ X
