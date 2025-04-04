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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical
open scoped InnerProductSpace

namespace PointedCone

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

end PointedCone

noncomputable section DualPolyhedral
open PointedCone

variable (S : Finset E) (w : E)

private abbrev inner_nonneg_set : Finset E := {s ∈ S | 0 ≤ ⟪s,w⟫_ℝ }
private abbrev inner_neg_set : Finset E := {s ∈ S | ⟪s,w⟫_ℝ < 0}

lemma inner_w_nonneg_of_mem_span (x : E) (hx : x ∈ span ℝ (inner_nonneg_set S w)) :
    ⟪x,w⟫_ℝ ≥ 0 := by
  revert x
  apply Submodule.span_induction
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
    exact hx.2
  · simp only [inner_zero_left, ge_iff_le, le_refl]
  · intro x y hx hy hxw hyw
    rw [inner_add_left]
    exact add_nonneg hxw hyw
  · intro ⟨t,ht⟩ x hx hxw
    rw [Nonneg.mk_smul, real_inner_smul_left]
    exact mul_nonneg ht hxw

private abbrev generating_set := inner_nonneg_set S w ∪
  Finset.image (fun (x,y) => ⟪x,w⟫_ℝ • y - ⟪y,w⟫_ℝ • x)
               (Finset.product (inner_nonneg_set S w) (inner_neg_set S w))

private lemma generating_set_le_span : (generating_set S w : Set E) ≤ span ℝ (S : Set E) := by
  intro x hx
  rw [Finset.mem_coe, Finset.mem_union] at hx
  rcases hx with (hx | hx)
  · apply Submodule.subset_span
    exact Finset.mem_of_mem_filter x hx
  · simp only [Finset.product_eq_sprod, Finset.mem_image, Finset.mem_product, Finset.mem_filter,
    Prod.exists] at hx
    obtain ⟨a,b,⟨⟨haS,haw⟩,⟨hbS,hbw⟩⟩,rfl⟩ := hx
    let t₁ : {t : ℝ // 0 ≤ t} := ⟨⟪a,w⟫_ℝ, haw⟩
    let t₂ : {t : ℝ // 0 ≤ t} := ⟨-⟪b,w⟫_ℝ, by rw [neg_nonneg]; exact le_of_lt hbw⟩
    rw [SetLike.mem_coe, sub_eq_add_neg, ←neg_smul]
    change t₁ • b + t₂ • a ∈ _
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact hbS
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact haS

private lemma generating_set_le_dual' : (generating_set S w : Set E) ≤ dual' {w} := by
  intro x hx
  simp only [Finset.coe_union, Finset.coe_filter, Finset.product_eq_sprod, Finset.coe_image,
    Finset.coe_product, Set.mem_union, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod,
    Prod.exists] at hx
  rcases hx with (⟨hxS, hxw⟩ | ⟨a,b,⟨⟨haS,haw⟩,⟨hbS,hbw⟩⟩,rfl⟩)
  · simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq]
    rw [real_inner_comm]
    exact hxw
  · simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq]
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, mul_comm,
        real_inner_comm]
    nth_rw 2 [real_inner_comm]
    rw [sub_self]

private lemma mem_span_generating_set {x y : E} (hx : x ∈ span ℝ (inner_nonneg_set S w))
  (hy : y ∈ span ℝ (inner_neg_set S w)) :
    ⟪x,w⟫_ℝ • y - ⟪y,w⟫_ℝ • x ∈ span ℝ (generating_set S w) := by
  revert x y
  apply Submodule.span_induction₂
  · intro x y hx hy
    apply Submodule.subset_span
    apply Finset.mem_union_right
    rw [Finset.mem_image]
    refine ⟨(x,y),?_,rfl⟩ 
    rw [Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨hx,hy⟩ 
  · intro x hx
    simp only [Finset.coe_union, Finset.coe_filter, Finset.product_eq_sprod, Finset.coe_image,
      Finset.coe_product, inner_zero_left, zero_smul, smul_zero, sub_self, Submodule.zero_mem]
  · intro x hx
    simp only [Finset.coe_union, Finset.coe_filter, Finset.product_eq_sprod, Finset.coe_image,
      Finset.coe_product, smul_zero, inner_zero_left, zero_smul, sub_self, Submodule.zero_mem]
  · intro x y z hx hy hz hxz hyz
    convert Submodule.add_mem _ hxz hyz using 1
    rw [inner_add_left, smul_add, add_smul]
    abel
  · intro x y z hx hy hz hxy hxz
    convert Submodule.add_mem _ hxy hxz using 1
    rw [inner_add_left, smul_add, add_smul]
    abel
  · intro ⟨t,ht⟩ x y hx hy hxy
    convert Submodule.smul_mem _ ⟨t,ht⟩ hxy using 1
    rw [Nonneg.mk_smul, real_inner_smul_left, Nonneg.mk_smul, smul_sub, smul_smul,
      smul_smul, smul_smul]
    nth_rw 2 [mul_comm]
  · intro ⟨t,ht⟩ x y hx hy hxy
    convert Submodule.smul_mem _ ⟨t,ht⟩ hxy using 1
    rw [Nonneg.mk_smul, real_inner_smul_left, Nonneg.mk_smul, smul_sub, smul_smul,
      smul_smul, smul_smul, mul_comm]

private lemma span_inf_dual'_eq_span_generating_set :
    span ℝ S ⊓ dual' {w} = span ℝ (generating_set S w) := by
  apply le_antisymm
  · intro x ⟨hx,hxw⟩ 
    simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq] at hxw
    revert x
    apply Submodule.span_induction
    · intro x hx hxw
      apply Submodule.subset_span
      apply Finset.mem_union_left
      rw [Finset.mem_filter, real_inner_comm]
      exact ⟨hx,hxw⟩ 
    · intro _
      exact Submodule.zero_mem _
    · intro x y hx hy hxw hyw hxyw
      rw [inner_add_right] at hxyw
      wlog H : 0 ≤ ⟪w,x⟫_ℝ generalizing x y
      · rw [add_comm] at hxyw ⊢
        apply this y x hy hx hyw hxw hxyw
        linarith
      · apply Submodule.add_mem _ (hxw H)
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
  · apply le_inf
    · exact Submodule.span_le.mpr (generating_set_le_span S w)
    · exact Submodule.span_le.mpr (generating_set_le_dual' S w)

lemma IsPolyhedral.inf_dual'_singleton {c : PointedCone ℝ E} (hc : c.IsPolyhedral) (w : E) :
    IsPolyhedral (c ⊓ dual' {w}) := by
  obtain ⟨S, rfl⟩ := hc
  use (generating_set S w)
  exact span_inf_dual'_eq_span_generating_set S w

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

end DualPolyhedral
