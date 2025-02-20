/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.Data.Complex.Basic
import Toric.Variety
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib

open AlgebraicGeometry CategoryTheory Topology
open scoped MonoidalCategory

variable {R : CommRingCat} {X Y : Scheme}

variable (R) in
noncomputable abbrev Torus (n : ℕ) : Variety R :=
  ⟨.mk <| AlgebraicGeometry.Spec.map <| CommRingCat.ofHom <| algebraMap R <|
      AddMonoidAlgebra R <| FreeAbelianGroup <| Fin n, sorry⟩

variable (R) (n : ℕ) in
def TorusSelfAction : Torus R n ⊗ Torus R n ⟶ Torus R n := sorry

variable (R) in
abbrev ToricVariety := FullSubcategory fun X :
  Σ n : ℕ,
  Σ X : Variety R,
  (Torus R n ⟶ X) × (Torus R n ⊗ X ⟶ X) ↦
  sorry
