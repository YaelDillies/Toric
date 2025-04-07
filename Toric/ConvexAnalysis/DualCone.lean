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


lemma inner_nonneg_of_mem_span_inner_nonneg (w : E) (S : Set E) (hS : ∀ x ∈ S, ⟪x,w⟫_ℝ ≥ 0)
    {x : E} (hx : x ∈ span ℝ S) : ⟪x,w⟫_ℝ ≥ 0 := by
  revert x
  apply Submodule.span_induction
  · exact hS
  · rw [inner_zero_left]
  · intro x y hx hy hxw hyw
    rw [inner_add_left]
    exact add_nonneg hxw hyw
  · intro ⟨t,ht⟩ x hx hxw
    rw [Nonneg.mk_smul, real_inner_smul_left]
    exact mul_nonneg ht hxw

lemma inner_nonpos_of_mem_span_inner_nonpos (w : E) (S : Set E) (hS : ∀ x ∈ S, ⟪x,w⟫_ℝ ≤ 0)
    {x : E} (hx : x ∈ span ℝ S) : ⟪x,w⟫_ℝ ≤ 0 := by
  revert x
  apply Submodule.span_induction
  · exact hS
  · rw [inner_zero_left]
  · intro x y hx hy hxw hyw
    rw [inner_add_left]
    exact add_nonpos hxw hyw
  · intro ⟨t,ht⟩ x hx hxw
    rw [Nonneg.mk_smul, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos ht hxw

lemma eq_zero_of_inner_eq_zero_of_mem_span_inner_pos (w : E) (S : Set E)
    (hS : ∀ x ∈ S, ⟪x,w⟫_ℝ > 0) {x : E} (hx₁ : x ∈ span ℝ S) (hx₂ : ⟪x,w⟫_ℝ = 0) : x = 0 := by
  revert x
  apply Submodule.span_induction
  · intro x hxS hxw
    specialize hS x hxS
    linarith
  · intro h
    rfl
  · intro x y hxS hyS hx hy hxyw
    rw [inner_add_left] at hxyw
    have H : ⟪x,w⟫_ℝ = 0 ∧ ⟪y,w⟫_ℝ = 0 := (add_eq_zero_iff_of_nonneg
      (inner_nonneg_of_mem_span_inner_nonneg w S (fun z hz => le_of_lt (hS z hz)) hxS)
      (inner_nonneg_of_mem_span_inner_nonneg w S (fun z hz => le_of_lt (hS z hz)) hyS)).mp hxyw
    rw [hx H.1, hy H.2]
    exact zero_add 0
  · intro ⟨t,ht⟩ x hxS hx hxw
    rw [Nonneg.mk_smul, real_inner_smul_left] at hxw
    rw [Nonneg.mk_smul]
    by_cases ht : t = 0
    · rw [ht, zero_smul]
    · rw [hx ((mul_eq_zero_iff_left ht).mp hxw), smul_zero]

lemma eq_zero_of_inner_eq_zero_of_mem_span_inner_neg (w : E) (S : Set E)
    (hS : ∀ x ∈ S, ⟪x,w⟫_ℝ < 0) {x : E} (hx₁ : x ∈ span ℝ S) (hx₂ : ⟪x,w⟫_ℝ = 0) : x = 0 := by
  revert x
  apply Submodule.span_induction
  · intro x hxS hxw
    specialize hS x hxS
    linarith
  · intro h
    rfl
  · intro x y hxS hyS hx hy hxyw
    rw [inner_add_left] at hxyw
    have H := (add_eq_zero_iff_of_nonneg
      (neg_nonneg_of_nonpos <|
        inner_nonpos_of_mem_span_inner_nonpos w S (fun z hz => le_of_lt (hS z hz)) hxS)
      (neg_nonneg_of_nonpos <|
        inner_nonpos_of_mem_span_inner_nonpos w S (fun z hz => le_of_lt (hS z hz)) hyS)).mp <| by
      rw [←neg_add, hxyw, neg_zero]
    rw [neg_eq_zero, neg_eq_zero] at H
    rw [hx H.1, hy H.2]
    exact zero_add 0
  · intro ⟨t,ht⟩ x hxS hx hxw
    rw [Nonneg.mk_smul, real_inner_smul_left] at hxw
    rw [Nonneg.mk_smul]
    by_cases ht : t = 0
    · rw [ht, zero_smul]
    · rw [hx ((mul_eq_zero_iff_left ht).mp hxw), smul_zero]

end PointedCone

noncomputable section DualPolyhedral
open PointedCone

variable (S : Finset E) (w : E)

private abbrev generating_set : Finset E :=
  {s ∈ S | ⟪s,w⟫_ℝ ≥ 0} ∪
  Finset.image (fun (x,y) => ⟪x,w⟫_ℝ • y - ⟪y,w⟫_ℝ • x)
               (Finset.product {x ∈ S | 0 ≤ ⟪x,w⟫_ℝ} {y ∈ S | ⟪y,w⟫_ℝ ≤ 0})

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
    let t₂ : {t : ℝ // 0 ≤ t} := ⟨-⟪b,w⟫_ℝ, neg_nonneg.mpr hbw⟩
    rw [SetLike.mem_coe, sub_eq_add_neg, ←neg_smul]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ t₁ (Submodule.subset_span hbS)) 
      (Submodule.smul_mem _ t₂ (Submodule.subset_span haS))

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

private lemma mem_span_generating_set {x y : E}
  (hx : x ∈ span ℝ {s ∈ S | 0 ≤ ⟪s,w⟫_ℝ})
  (hy : y ∈ span ℝ {s ∈ S | ⟪s,w⟫_ℝ ≤ 0}) :
    ⟪x,w⟫_ℝ • y - ⟪y,w⟫_ℝ • x ∈ span ℝ (generating_set S w) := by
  revert x y
  apply Submodule.span_induction₂
  · intro x y hx hy
    apply Submodule.subset_span
    apply Finset.mem_union_right
    rw [Finset.mem_image]
    refine ⟨(x,y),?_,rfl⟩ 
    rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
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
  · intro v ⟨h₁,h₂⟩
    simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq] at h₂
    -- We write S as the union of elements with nonnegative resp. negative inner
    -- product with w.
    have S_eq_union : S = {s ∈ S | 0 ≤ ⟪s,w⟫_ℝ} ∪ {s ∈ S | ⟪s,w⟫_ℝ < 0} := by
      ext s
      constructor
      · intro hs
        by_cases H : 0 ≤ ⟪s,w⟫_ℝ
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs,H⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs,lt_of_not_ge H⟩)
      · rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rintro (hs|hs) <;> exact hs.1
    rw [S_eq_union, PointedCone.span, Finset.coe_union, Submodule.span_union,
      SetLike.mem_coe, Submodule.mem_sup] at h₁
    obtain ⟨x,hx,y,hy,hv⟩ := h₁
    rw [real_inner_comm, ←hv, inner_add_left] at h₂
    have x_mem : x ∈ span ℝ (generating_set S w) :=
      Submodule.span_mono Finset.subset_union_left hx
    rw [Finset.coe_filter] at hx hy
    have hxw : 0 ≤ ⟪x,w⟫_ℝ := inner_nonneg_of_mem_span_inner_nonneg w _ (fun z hz => hz.2) hx
    have hyw : ⟪y,w⟫_ℝ ≤ 0 := inner_nonpos_of_mem_span_inner_nonpos w _
      (fun z hz => le_of_lt hz.2) hy
    by_cases H : ⟪x,w⟫_ℝ = 0
    · rw [H, zero_add] at h₂
      rw [←hv]
      apply Submodule.add_mem _ x_mem
      convert Submodule.zero_mem _
      exact eq_zero_of_inner_eq_zero_of_mem_span_inner_neg w _ (fun x hx => hx.2) hy <|
        le_antisymm hyw h₂
    · let u : E := ⟪x,w⟫_ℝ • y - ⟪y,w⟫_ℝ • x
      have u_mem : u ∈ span ℝ (generating_set S w) := mem_span_generating_set S w hx <|
        Submodule.span_mono (fun z hz => And.intro hz.1 (le_of_lt hz.2)) hy
      have t₂_nonneg : 0 ≤ (⟪x,w⟫_ℝ)⁻¹ := inv_nonneg_of_nonneg hxw
      have t₁_nonneg : 0 ≤ 1 + ⟪y,w⟫_ℝ * (⟪x,w⟫_ℝ)⁻¹ := by
        convert mul_le_mul_of_nonneg_right h₂ t₂_nonneg using 1
        · rw [zero_mul]
        · rw [add_mul, mul_inv_cancel₀ H]
      let t₁ : {t : ℝ // 0 ≤ t} := ⟨_,t₁_nonneg⟩
      let t₂ : {t : ℝ // 0 ≤ t} := ⟨_,t₂_nonneg⟩
      have v_eq : v = t₁ • x + t₂ • u := by rw [Nonneg.mk_smul, Nonneg.mk_smul, add_smul,
        smul_sub, smul_smul, inv_mul_cancel₀ H, smul_smul, mul_comm, add_add_sub_cancel,
        one_smul, one_smul, hv]
      rw [v_eq]
      apply Submodule.add_mem
      · apply Submodule.smul_mem
        exact x_mem
      · apply Submodule.smul_mem
        exact u_mem
  · apply le_inf
    · rw [Submodule.span_le]
      exact generating_set_le_span S w
    · rw [Submodule.span_le]
      exact generating_set_le_dual' S w

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
