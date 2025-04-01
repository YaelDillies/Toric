/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Justus Springer
-/
import Mathlib.Analysis.Convex.Cone.Pointed

/-!
# Lemmas

Prove some lemmas about the dual cone.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s t : PointedCone ℝ E)

lemma PointedCone.dual_le_dual (h : s ≤ t) : t.dual ≤ s.dual := by
  intro x hx y hy
  exact hx y (h hy)

lemma PointedCone.dual_add : (s + t).dual = s.dual ⊓ t.dual := by
  ext x
  constructor
  · intro hx
    split_ands
    · exact PointedCone.dual_le_dual s (s ⊔ t) le_sup_left hx
    · exact PointedCone.dual_le_dual t (s ⊔ t) le_sup_right hx
  · intro ⟨hxs,hxt⟩ y hy
    rw [SetLike.mem_coe] at hxs hxt hy
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hy
    obtain ⟨a,ha,b,hb,rfl⟩ := hy
    rw [inner_add_left]
    apply add_nonneg (hxs a ha) (hxt b hb)
