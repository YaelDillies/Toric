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

open Classical
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The dual of an arbitrary set as a `PointedCone`. -/
def dual' (S : Set E) : PointedCone ℝ E :=
  (S.innerDualCone).toPointedCone <| pointed_innerDualCone S

@[simp, norm_cast]
theorem toConvexCone_dual' (S : Set E) : ↑(dual' S) = (S : Set E).innerDualCone :=
  rfl

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

lemma IsPolyhedral.inf_dual'_singleton {c : PointedCone ℝ E} (hc : c.IsPolyhedral) (w : E) :
    IsPolyhedral (c ⊓ dual' {w}) := by
  obtain ⟨S, rfl⟩ := hc
  let Sₚ : Finset E := {s ∈ S | ⟪s,w⟫_ℝ > 0}
  let S₀ : Finset E := {s ∈ S | ⟪s,w⟫_ℝ = 0}
  let Sₙ : Finset E := {s ∈ S | ⟪s,w⟫_ℝ < 0}
  let T := S₀ ∪ Sₚ ∪ Finset.image (fun (x,y) => ⟪x,w⟫_ℝ • y - ⟪y,w⟫_ℝ • x) (Finset.product Sₚ Sₙ)
  use T
  apply le_antisymm
  · intro x ⟨hx₁, hx₂⟩ 
    simp only [SetLike.mem_coe] at hx₁
    simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq] at hx₂
    revert x
    apply Submodule.span_induction
    · intro x hxS hxw
      apply Submodule.subset_span
      apply Finset.mem_union_left
      by_cases hxwzero : ⟪x, w⟫_ℝ = 0
      · apply Finset.mem_union_left
        rw [Finset.mem_filter]
        exact ⟨hxS, hxwzero⟩
      · apply Finset.mem_union_right
        rw [Finset.mem_filter]
        refine ⟨hxS, lt_of_le_of_ne ?_ (Ne.symm hxwzero)⟩
        rw [real_inner_comm]
        exact hxw
    · intro _
      exact Submodule.zero_mem _
    · intro x y hxS hyS hwx hwy hwxy
      rw [inner_add_right] at hwxy
      by_cases h : ⟪w,x⟫_ℝ ≥ 0 ∧ ⟪w,y⟫_ℝ ≥ 0
      · exact Submodule.add_mem _ (hwx h.1) (hwy h.2)
      · rw [not_and_or] at h
        wlog H : ⟪w,x⟫_ℝ < 0 generalizing x y
        · sorry
        · clear hwx
          have hwy_pos : ⟪w,y⟫_ℝ > 0 := sorry
          specialize hwy (le_of_lt hwy_pos)
          refine Submodule.add_mem _ ?_ hwy
          sorry
    · intro ⟨t,ht⟩ x hxS hwx hwtx
      by_cases htzero : t = 0
      · rw [Nonneg.mk_smul, htzero, zero_smul]
        exact Submodule.zero_mem _
      · have tpos : t > 0 := lt_of_le_of_ne ht (Ne.symm htzero)
        apply Submodule.smul_mem
        apply hwx
        rw [Nonneg.mk_smul, real_inner_smul_right] at hwtx
        exact nonneg_of_mul_nonneg_right hwtx tpos
  · rw [Submodule.span_le]
    intro x hxT
    split_ands
    · rw [Finset.mem_coe, Finset.mem_union, Finset.mem_union] at hxT
      rcases hxT with (hxS₀ | hxSₚ) | hxT
      · apply Submodule.subset_span
        rw [Finset.mem_coe]
        exact Finset.mem_of_mem_filter x hxS₀
      · apply Submodule.subset_span
        rw [Finset.mem_coe]
        exact Finset.mem_of_mem_filter x hxSₚ
      · simp only [Finset.product_eq_sprod, Finset.mem_image, Finset.mem_product,
        Prod.exists] at hxT
        obtain ⟨a,b,⟨ha,hb⟩,rfl⟩ := hxT
        rw [Finset.mem_filter] at ha hb
        obtain ⟨haS, haw⟩ := ha
        obtain ⟨hbS, hbw⟩ := hb
        rw [SetLike.mem_coe, sub_eq_add_neg, ←neg_smul]
        let t₁ : {t : ℝ // 0 ≤ t} := ⟨⟪a,w⟫_ℝ, le_of_lt haw⟩
        let t₂ : {t : ℝ // 0 ≤ t} := ⟨-⟪b,w⟫_ℝ, by rw [neg_nonneg]; exact le_of_lt hbw⟩
        change t₁ • b + t₂ • a ∈ _
        apply Submodule.add_mem
        · apply Submodule.smul_mem
          apply Submodule.subset_span
          exact hbS
        · apply Submodule.smul_mem
          apply Submodule.subset_span
          exact haS
    · simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq]
      rw [Finset.mem_coe, Finset.mem_union, Finset.mem_union] at hxT
      rcases hxT with (hxS₀ | hxSₚ) | hxT
      · rw [Finset.mem_filter] at hxS₀
        obtain ⟨_,h⟩ := hxS₀
        rw [real_inner_comm, h]
      · rw [Finset.mem_filter] at hxSₚ
        obtain ⟨_,h⟩ := hxSₚ
        rw [real_inner_comm]
        exact le_of_lt h
      · simp only [Finset.product_eq_sprod, Finset.mem_image, Finset.mem_product,
        Prod.exists] at hxT
        obtain ⟨a,b,⟨ha,hb⟩,rfl⟩ := hxT
        rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, mul_comm,
            real_inner_comm]
        nth_rw 2 [real_inner_comm]
        rw [sub_self]

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
