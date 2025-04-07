/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Spherical varieties

This file defines a spherical variety over `B` over a ring `R` as a scheme `X` over `Spec R`
equipped with an action `B × X → X` with an open orbit.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry
variable {R : CommRingCat} {n : ℕ} {X Y : Scheme}

variable (R n)
/-- A spherical variety over `B` over a ring `R` is a scheme `X` equipped with an action `B × X → X`
with an open orbit. -/
class SphericalVariety (B X : Scheme) [B.Over (Spec R)] extends X.Over (Spec R) where
  act : pullback (B ↘ Spec R) (X ↘ Spec R) ⟶ X

end AlgebraicGeometry
