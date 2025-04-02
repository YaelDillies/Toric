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

open Classical

namespace PointedCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


/-- The dual of an arbitrary set as a `PointedCone`. -/
def dual' (S : Set E) : PointedCone ℝ E :=
  (S.innerDualCone).toPointedCone <| pointed_innerDualCone S

@[simp, norm_cast]
theorem toConvexCone_dual' (S : Set E) : ↑(dual' S) = (S : Set E).innerDualCone :=
  rfl

open scoped InnerProductSpace in
@[simp]
theorem mem_dual' {S : Set E} {y : E} : y ∈ dual' S ↔ ∀ ⦃x⦄, x ∈ S → 0 ≤ ⟪x, y⟫_ℝ := by
  rfl

lemma dual'_le_dual' {s t : Set E} (h : s ⊆ t) : dual' t ≤ dual' s := by
  intro x hx y hy
  exact hx y (h hy)

lemma dual'_union {s t : Set E} : dual' (s ∪ t) = dual' s ⊓ dual' t := by
  ext x
  constructor
  · intro hx
    split_ands
    · exact dual'_le_dual' (t := s ⊔ t) le_sup_left hx
    · exact dual'_le_dual' (t := s ⊔ t) le_sup_right hx
  · rintro ⟨hxs,hxt⟩ y (hy|hy)
    · exact hxs y hy
    · exact hxt y hy

lemma span_dual_eq {s : Set E} :
    (span ℝ s).dual = dual' s := by
  apply le_antisymm
  · apply innerDualCone_le_innerDualCone
    exact subset_span
  · intro x hx
    rw [mem_dual]
    apply Submodule.span_induction
    · intro y hy
      exact hx y hy
    · simp only [inner_zero_left, le_refl]
    · intro y z _ _ hxy hyz
      rw [inner_add_left]
      exact add_nonneg hxy hyz
    · intro t y _ hxy 
      erw [inner_smul_real_left]
      exact mul_nonneg t.prop hxy

lemma IsPolyhedral.inf_dual'_singleton {c : PointedCone ℝ E} (hc : c.IsPolyhedral) (x : E) :
    IsPolyhedral (c ⊓ dual' {x}) :=
  sorry

theorem IsPolyhedral.dual [FiniteDimensional ℝ E] {c : PointedCone ℝ E} (hc : c.IsPolyhedral) :
    c.dual.IsPolyhedral := by
  obtain ⟨S,rfl⟩ := hc
  rw [span_dual_eq]
  revert S
  apply Finset.induction
  · convert IsPolyhedral.top (𝕜 := ℝ) (E := E)
    apply toConvexCone_injective
    rw [toConvexCone_dual', Finset.coe_empty, innerDualCone_empty]
    rfl
  · intro x S hx hS
    rw [Finset.insert_eq, Finset.coe_union, dual'_union, inf_comm, Finset.coe_singleton]
    apply IsPolyhedral.inf_dual'_singleton
    exact hS

theorem IsPolyhedral.dual_dual [FiniteDimensional ℝ E] {c : PointedCone ℝ E} :
    c.dual.dual = c := by
  sorry

end PointedCone
