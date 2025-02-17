/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.Data.Complex.Basic
import Toric.Variety

open AlgebraicGeometry CategoryTheory Topology
open scoped MonoidalCategory

variable {R : CommRingCat} {X Y : Scheme}

variable (R) in
abbrev Torus (n : ℕ) : Variety R := sorry

variable (R) in
abbrev ToricVariety := FullSubcategory fun X :
  Σ n : ℕ,
  Σ X : Variety R,
  (Torus R n ⟶ X) × (Torus R n ⊗ X ⟶ X) ↦
  sorry
