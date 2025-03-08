/-
Copyright (c) 2025 Matthew Johnson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Johnson, Yaël Dillies
-/
import Mathlib

variable {N : Type*} [AddCommGroup N] [Module ℝ N]

def IsPolytope (s : Set N) : Prop := ∃ t : Finset N, s = convexHull ℝ t

@[simp]
lemma IsPolytope.empty : IsPolytope (∅ : Set N) := by
  unfold IsPolytope
  use ∅
  simp

@[simp]
lemma IsPolytope.singleton (x : N) : IsPolytope {x} := by
  unfold IsPolytope
  use {x}
  simp

@[simp]
theorem IsPolytope.convexHull_Finset (s : Finset N) : IsPolytope <| convexHull ℝ s.toSet := by
  use s

@[simp]
theorem IsPolytope.segment (x y : N) : IsPolytope <| segment ℝ x y := by
  unfold IsPolytope
  classical
  use {x,y}
  simp
