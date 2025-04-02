/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Justus Springer
-/
import Mathlib.Analysis.Convex.Cone.Pointed
import Toric.ConvexAnalysis.PolyhedralCone

/-!
# Lemmas

Prove some lemmas about the dual cone.
-/

namespace PointedCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma dual_le_dual {s t : PointedCone ℝ E} (h : s ≤ t) : t.dual ≤ s.dual := by
  intro x hx y hy
  exact hx y (h hy)

lemma dual_add {s t : PointedCone ℝ E} : (s + t).dual = s.dual ⊓ t.dual := by
  ext x
  constructor
  · intro hx
    split_ands
    · exact dual_le_dual (t := s ⊔ t) le_sup_left hx
    · exact dual_le_dual (t := s ⊔ t) le_sup_right hx
  · intro ⟨hxs,hxt⟩ y hy
    rw [SetLike.mem_coe] at hxs hxt hy
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hy
    obtain ⟨a,ha,b,hb,rfl⟩ := hy
    rw [inner_add_left]
    apply add_nonneg (hxs a ha) (hxt b hb)

theorem IsPolyhedral.dual {c : PointedCone ℝ E} (hc : c.IsPolyhedral) : c.dual.IsPolyhedral := by
  sorry

theorem IsPolyhedral.dual_dual {c : PointedCone ℝ E} : c.dual.dual = c := by
  sorry

end PointedCone
