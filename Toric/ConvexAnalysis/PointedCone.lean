/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Justus Springer
-/
import Mathlib.Analysis.Convex.Cone.Pointed
import Toric.ConvexAnalysis.PolyhedralCone

/-!
# Pointed cones

We prove that the dual of a polyhedral cone is polyhedral.

-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical
open scoped InnerProductSpace

namespace PointedCone

section Dual

variable (S : Set E) (w : E)

/-- The dual of an arbitrary set as a `PointedCone`. -/
def dual' : PointedCone ℝ E :=
  S.innerDualCone.toPointedCone <| pointed_innerDualCone S

@[simp, norm_cast]
theorem toConvexCone_dual' : ↑(dual' S) = (S : Set E).innerDualCone :=
  rfl

lemma dual_eq_dual' {σ : PointedCone ℝ E} : σ.dual = dual' (σ : Set E) :=
  rfl

@[simp]
theorem mem_dual' {S : Set E} {y : E} : y ∈ dual' S ↔ ∀ ⦃x⦄, x ∈ S → 0 ≤ ⟪x, y⟫_ℝ :=
  Iff.rfl

lemma dual'_le_dual' {s t : Set E} (h : s ⊆ t) : dual' t ≤ dual' s :=
  fun _ hx y hy => hx y (h hy)

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

/-- A generating set for `span ℝ S ⊓ dual' {w}`, see `span_inf_dual'_singleton_eq_span -/
abbrev inf_dual'_singleton_generating_set : Set E :=
  {s ∈ S | 0 ≤ ⟪s,w⟫_ℝ} ∪
  Set.image2 (fun x y => ⟪x, w⟫_ℝ • y - ⟪y, w⟫_ℝ • x) {s ∈ S | 0 ≤ ⟪s,w⟫_ℝ} {s ∈ S | ⟪s,w⟫_ℝ ≤ 0}

lemma mem_span_inf_dual'_singleton_generating_set {x y : E}
  (hx : x ∈ span ℝ {s ∈ S | 0 ≤ ⟪s,w⟫_ℝ})
  (hy : y ∈ span ℝ {s ∈ S | ⟪s,w⟫_ℝ ≤ 0}) :
    ⟪x, w⟫_ℝ • y - ⟪y, w⟫_ℝ • x ∈ span ℝ (inf_dual'_singleton_generating_set S w) := by
  revert x y
  apply Submodule.span_induction₂
  · intro x y hx hy
    apply Submodule.subset_span
    apply Set.subset_union_right
    exact ⟨x,hx,y,hy,rfl⟩
  · intro x hx
    simp only [inner_zero_left, zero_smul, smul_zero, sub_self, Submodule.zero_mem]
  · intro x hx
    simp only [smul_zero, inner_zero_left, zero_smul, sub_self, Submodule.zero_mem]
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

lemma span_inf_dual'_singleton_eq_span :
    span ℝ S ⊓ dual' {w} = span ℝ (inf_dual'_singleton_generating_set S w) := by
  apply le_antisymm
  · intro v ⟨h₁,h₂⟩
    simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq] at h₂
    -- We split `S` into the subset of elements with inner product nonnegative resp. negative.
    have S_eq_union : S = {s ∈ S | 0 ≤ ⟪s,w⟫_ℝ} ∪ {s ∈ S | ⟪s,w⟫_ℝ < 0} := by
      ext s
      simp only [Set.mem_union, Set.mem_setOf_eq]
      constructor
      · intro hs
        by_cases H : 0 ≤ ⟪s,w⟫_ℝ
        · exact Or.inl ⟨hs,H⟩
        · exact Or.inr ⟨hs,lt_of_not_ge H⟩
      · rintro (hs|hs) <;> exact hs.1
    rw [S_eq_union, PointedCone.span, Submodule.span_union,
      SetLike.mem_coe, Submodule.mem_sup] at h₁
    -- Let's write `v` as `x+y`, where `x` is in the span of elements with nonnegative
    -- inner product with `w` and `y` is in the span of elements with negative inner product
    -- with `w`.
    obtain ⟨x,hx,y,hy,hv⟩ := h₁
    rw [real_inner_comm, ←hv, inner_add_left] at h₂
    have x_mem : x ∈ span ℝ (inf_dual'_singleton_generating_set S w) :=
      Submodule.span_mono Set.subset_union_left hx
    -- Clearly, `x` itself has nonnegative inner product with `w`, while `y` has negative
    -- inner product
    have hxw : 0 ≤ ⟪x, w⟫_ℝ := inner_nonneg_of_mem_span_inner_nonneg (fun z hz => hz.2) hx
    have hyw : ⟪y, w⟫_ℝ ≤ 0 := inner_nonpos_of_mem_span_inner_nonpos (fun z hz => hz.2.le) hy
    -- We treat the case `⟪x, w⟫_ℝ` = 0 seperately.
    by_cases H : ⟪x, w⟫_ℝ = 0
    · rw [H, zero_add] at h₂
      rw [←hv]
      apply Submodule.add_mem _ x_mem
      convert Submodule.zero_mem _
      -- Since `y` is in the span of elements with negative inner product with `w`, but itself
      -- has `⟪y, w⟫_ℝ = 0`, `y` must be zero.
      exact eq_zero_of_inner_eq_zero_of_mem_span_inner_neg w _ (fun x hx => hx.2) hy <|
        le_antisymm hyw h₂
    · let u : E := ⟪x, w⟫_ℝ • y - ⟪y, w⟫_ℝ • x
      have u_mem : u ∈ span ℝ (inf_dual'_singleton_generating_set S w) :=
        mem_span_inf_dual'_singleton_generating_set S w hx <|
          Submodule.span_mono (fun z hz => And.intro hz.1 (le_of_lt hz.2)) hy
      have t₂_nonneg : 0 ≤ (⟪x, w⟫_ℝ)⁻¹ := inv_nonneg_of_nonneg hxw
      have t₁_nonneg : 0 ≤ 1 + ⟪y, w⟫_ℝ * (⟪x, w⟫_ℝ)⁻¹ := by
        convert mul_le_mul_of_nonneg_right h₂ t₂_nonneg using 1
        · rw [zero_mul]
        · rw [add_mul, mul_inv_cancel₀ H]
      let t₁ : {t : ℝ // 0 ≤ t} := ⟨_,t₁_nonneg⟩
      let t₂ : {t : ℝ // 0 ≤ t} := ⟨_,t₂_nonneg⟩
      -- With the above definitions, a computation shows that `v = t₁ • x + t₂ • y`.
      have v_eq : v = t₁ • x + t₂ • u := by rw [Nonneg.mk_smul, Nonneg.mk_smul, add_smul,
        smul_sub, smul_smul, inv_mul_cancel₀ H, smul_smul, mul_comm, add_add_sub_cancel,
        one_smul, one_smul, hv]
      rw [v_eq]
      -- But both `x` and `u` are in the span and `t₁` and `t₂` are nonnegative, hence
      -- we are done.
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ x_mem) (Submodule.smul_mem _ _ u_mem)
  · rw [Submodule.span_le]
    apply le_inf
    · intro v hv
      rcases hv with (hv | hv)
      · exact Submodule.subset_span hv.1
      · simp only [Set.mem_image2, Set.mem_setOf_eq] at hv
        obtain ⟨x,⟨hxS,hxw⟩,y,⟨hyS,hyw⟩,rfl⟩ := hv
        let t₁ : {t : ℝ // 0 ≤ t} := ⟨⟪x, w⟫_ℝ, hxw⟩
        let t₂ : {t : ℝ // 0 ≤ t} := ⟨-⟪y, w⟫_ℝ, neg_nonneg.mpr hyw⟩
        rw [SetLike.mem_coe, sub_eq_add_neg, ←neg_smul]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ t₁ (Submodule.subset_span hyS))
          (Submodule.smul_mem _ t₂ (Submodule.subset_span hxS))
    · intro x hx
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_image2] at hx
      rcases hx with (⟨hxS, hxw⟩ | ⟨x,⟨hxS,hxw⟩,y,⟨hyS,hyw⟩,rfl⟩)
      · simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq]
        rw [real_inner_comm]
        exact hxw
      · simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq]
        rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, mul_comm,
          real_inner_comm]
        nth_rw 2 [real_inner_comm]
        rw [sub_self]

lemma IsPolyhedral.inf_dual'_singleton {c : PointedCone ℝ E} (hc : c.IsPolyhedral) (w : E) :
    IsPolyhedral (c ⊓ dual' {w}) := by
  obtain ⟨S, rfl⟩ := hc
  have S_finite : (S : Set E).Finite := Finset.finite_toSet S
  have : (inf_dual'_singleton_generating_set S w).Finite := Set.Finite.union
    (Set.Finite.subset S_finite (fun s hs => hs.1))
    (Set.Finite.image2 _
      (Set.Finite.subset S_finite (fun s hs => hs.1))
      (Set.Finite.subset S_finite (fun s hs => hs.1)))
  use this.toFinset
  rw [span_inf_dual'_singleton_eq_span (S : Set E) w]
  simp only [Set.toFinite_toFinset, Set.toFinset_union, Finset.mem_coe, Set.toFinset_image2,
    Finset.coe_union, Set.coe_toFinset, Finset.coe_image₂]
  rfl

/-- The dual of a polyhedral cone is polyhedral. -/
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

end Dual

end PointedCone
