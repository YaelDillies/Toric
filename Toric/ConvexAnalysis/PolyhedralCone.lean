/-
Copyright (c) 2025 Paul Reichert, Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert, Justus Springer
-/
import Toric.Mathlib.Analysis.Convex.Cone.Pointed

/-!
# Pointed cone hull and polyhedral cones

We define the pointed cone hull and what it means for a pointed cone to be polyhedral.
-/

variable {𝕜 R E : Type*}

open scoped InnerProductSpace

namespace PointedCone
section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E] {s : Set E}

/-- A pointed cone is polyhedral if it is the convex hull of finitely many points. -/
def IsPolyhedral (c : PointedCone R E) : Prop := ∃ t : Finset E, PointedCone.span R t = c

protected lemma IsPolyhedral.span (h : s.Finite) : (span R s).IsPolyhedral := ⟨h.toFinset, by simp⟩

@[simp] lemma IsPolyhedral.bot : (⊥ : PointedCone R E).IsPolyhedral := ⟨{0}, by simp⟩

end OrderedSemiring

section LinearOrderedField
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- `⊤` is a polyhedral cone in a finite dimensional vector space over a linear ordered field. -/
@[simp]
lemma IsPolyhedral.top [hE : FiniteDimensional 𝕜 E] : (⊤ : PointedCone 𝕜 E).IsPolyhedral := by
  classical
  obtain ⟨S, hS⟩ := Module.finite_def.mp hE
  -- We take R to be the union of S with {-x | x ∈ S}
  let R : Finset E := S ∪ S.map (Function.Embedding.mk (Neg.neg : E → E) neg_injective)
  -- We first show that the span of R is closed under negation
  have neg_mem_span_R : ∀ x ∈ span 𝕜 R, (-x : E) ∈ span 𝕜 R := by
    apply Submodule.span_induction
    · intro x hx
      apply Submodule.subset_span
      -- Clearly, T is closed under negation. We show this by simple case distinction
      rw [Finset.mem_coe, Finset.mem_union] at hx
      cases' hx with hx₁ hx₂
      · apply Finset.mem_union_right
        simpa only [Finset.mem_map, Function.Embedding.coeFn_mk, neg_inj, exists_eq_right]
      · rw [Finset.mem_map, Function.Embedding.coeFn_mk] at hx₂
        obtain ⟨y, hy1, rfl⟩ := hx₂
        rw [neg_neg]
        exact Finset.mem_union_left _ hy1
    -- The three other cases in the induction are trivial
    · simp
    · intro x y _ _ hx hy
      rw [neg_add_rev]
      exact Submodule.add_mem _ hy hx
    · intro t x _ hx
      rw [←smul_neg]
      exact Submodule.smul_mem _ _ hx
  -- We now claim that `⊤` is generated as a pointed cone by `R`.
  use R
  rw [Submodule.eq_top_iff']
  rw [Submodule.eq_top_iff'] at hS
  intro x
  specialize hS x
  revert hS x
  -- By reverting x, the claim now says that every element of the span of S
  -- (as a usual `ℝ`-submodule) is contained in the span of `R` as a pointed cone.
  -- This can be shown by induction on the span.
  apply Submodule.span_induction
  · intro x hxS
    apply Submodule.subset_span
    exact Finset.mem_union_left _ hxS
  · apply Submodule.zero_mem
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro t x _ hx
    -- This is the only interesting case, as here we have split cases
    -- according to whether the scalar `t` is positive or not.
    by_cases ht : 0 ≤ t
    · exact Submodule.smul_mem _ ⟨t, ht⟩ hx
    · rw [← neg_neg (t • x), ← neg_smul, ← smul_neg]
      apply Submodule.smul_mem _ (⟨-t, by linarith⟩ : {a : 𝕜 // 0 ≤ a})
      -- We use our auxiliary statement from above
      exact neg_mem_span_R _ hx

end LinearOrderedField

section NormedAddCommGroup
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] {S : Finset E} {w x y : E}

/-- A generating set for `span ℝ S ⊓ dual' {w}`, see `span_inf_dual'_singleton_eq_span -/
private noncomputable abbrev infDualSingletonGenSet (S : Finset E) (w : E) : Finset E :=
  open scoped Classical in
  {s ∈ S | 0 ≤ ⟪s, w⟫_ℝ} ∪
    .image₂ (fun x y => ⟪x, w⟫_ℝ • y - ⟪y, w⟫_ℝ • x) {s ∈ S | 0 ≤ ⟪s, w⟫_ℝ} {s ∈ S | ⟪s, w⟫_ℝ ≤ 0}

private lemma mem_span_infDualSingletonGenSet (hx : x ∈ span ℝ {s ∈ S | 0 ≤ ⟪s, w⟫_ℝ})
    (hy : y ∈ span ℝ {s ∈ S | ⟪s, w⟫_ℝ ≤ 0}) :
    ⟪x, w⟫_ℝ • y - ⟪y, w⟫_ℝ • x ∈ span ℝ (infDualSingletonGenSet S w) := by
  classical
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    apply Submodule.subset_span
    apply Finset.subset_union_right
    simpa using ⟨x, hx, y, hy, rfl⟩
  | zero_left x hx =>
    simp only [inner_zero_left, zero_smul, smul_zero, sub_self, Submodule.zero_mem]
  | zero_right x hx =>
    simp only [smul_zero, inner_zero_left, zero_smul, sub_self, Submodule.zero_mem]
  | add_left x y z hx hy hz hxz hyz =>
    convert Submodule.add_mem _ hxz hyz using 1
    rw [inner_add_left, smul_add, add_smul]
    abel
  | add_right x y z hx hy hz hxy hxz =>
    convert Submodule.add_mem _ hxy hxz using 1
    rw [inner_add_left, smul_add, add_smul]
    abel
  | smul_left t x y hx hy hxy =>
    convert Submodule.smul_mem _ t hxy using 1
    rw [Nonneg.mk_smul, real_inner_smul_left, Nonneg.mk_smul, smul_sub, smul_smul,
      smul_smul, smul_smul]
    nth_rw 2 [mul_comm]
  | smul_right t x y hx hy hxy =>
    convert Submodule.smul_mem _ t hxy using 1
    rw [Nonneg.mk_smul, real_inner_smul_left, Nonneg.mk_smul, smul_sub, smul_smul,
      smul_smul, smul_smul, mul_comm]

variable (S w) in
private lemma span_infDualSingletonGenSet :
    span ℝ (infDualSingletonGenSet S w) = span ℝ S ⊓ dual' {w} := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    apply le_inf
    · intro v hv
      simp only [Finset.coe_union, Finset.coe_filter, Finset.coe_image₂, Set.mem_union,
        Set.mem_setOf_eq, Set.mem_image2] at hv
      obtain (hv | ⟨x, ⟨hxS, hxw⟩, y, ⟨hyS, hyw⟩, rfl⟩) := hv
      · exact Submodule.subset_span hv.1
      · let t₁ : {t : ℝ // 0 ≤ t} := ⟨⟪x, w⟫_ℝ, hxw⟩
        let t₂ : {t : ℝ // 0 ≤ t} := ⟨-⟪y, w⟫_ℝ, neg_nonneg.mpr hyw⟩
        rw [SetLike.mem_coe, sub_eq_add_neg, ← neg_smul]
        exact add_mem
          (Submodule.smul_mem _ t₁ (Submodule.subset_span hyS))
          (Submodule.smul_mem _ t₂ (Submodule.subset_span hxS))
    · intro x hx
      simp only [Finset.coe_union, Finset.coe_filter, Finset.coe_image₂, Set.mem_union,
        Set.mem_setOf_eq, Set.mem_image2] at hx
      obtain (⟨hxS, hxw⟩ | ⟨x, ⟨hxS, hxw⟩, y, ⟨hyS, hyw⟩, rfl⟩) := hx
      · simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq]
        rw [real_inner_comm]
        exact hxw
      · simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq]
        rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, mul_comm,
          real_inner_comm]
        nth_rw 2 [real_inner_comm]
        rw [sub_self]
  · intro v ⟨h₁, h₂⟩
    simp only [SetLike.mem_coe, mem_dual', Set.mem_singleton_iff, forall_eq] at h₂
    -- We split `S` into the subset of elements with inner product nonnegative resp. negative.
    have S_eq_union : S = {s ∈ S | 0 ≤ ⟪s, w⟫_ℝ} ∪ {s ∈ S | ⟪s, w⟫_ℝ < 0} := by
      simp [← Finset.filter_or, le_or_lt]
    rw [S_eq_union, Finset.coe_union, PointedCone.span, Submodule.span_union,
      SetLike.mem_coe, Submodule.mem_sup] at h₁
    -- Let's write `v` as `x+y`, where `x` is in the span of elements with nonnegative
    -- inner product with `w` and `y` is in the span of elements with negative inner product
    -- with `w`.
    obtain ⟨x, hx, y, hy, hv⟩ := h₁
    rw [real_inner_comm, ← hv, inner_add_left] at h₂
    have x_mem : x ∈ span ℝ (infDualSingletonGenSet S w) :=
      Submodule.span_mono Finset.subset_union_left hx
    -- Clearly, `x` itself has nonnegative inner product with `w`, while `y` has negative
    -- inner product
    simp only [Finset.coe_filter] at hx hy
    have hxw : 0 ≤ ⟪x, w⟫_ℝ := inner_nonneg_of_mem_span_inner_nonneg (fun z hz => hz.2) hx
    have hyw : ⟪y, w⟫_ℝ ≤ 0 := inner_nonpos_of_mem_span_inner_nonpos (fun z hz => hz.2.le) hy
    -- We treat the case `⟪x, w⟫_ℝ` = 0 seperately.
    by_cases H : ⟪x, w⟫_ℝ = 0
    · rw [H, zero_add] at h₂
      rw [← hv]
      apply Submodule.add_mem _ x_mem
      convert Submodule.zero_mem _
      -- Since `y` is in the span of elements with negative inner product with `w`, but itself
      -- has `⟪y, w⟫_ℝ = 0`, `y` must be zero.
      exact eq_zero_of_inner_eq_zero_of_mem_span_inner_neg (fun x hx => hx.2) hy <|
        le_antisymm hyw h₂
    · let u : E := ⟪x, w⟫_ℝ • y - ⟪y, w⟫_ℝ • x
      have u_mem : u ∈ span ℝ (infDualSingletonGenSet S w) :=
        mem_span_infDualSingletonGenSet hx <|
          Submodule.span_mono (fun z hz => And.intro hz.1 (le_of_lt hz.2)) hy
      have t₂_nonneg : 0 ≤ (⟪x, w⟫_ℝ)⁻¹ := inv_nonneg_of_nonneg hxw
      have t₁_nonneg : 0 ≤ 1 + ⟪y, w⟫_ℝ * (⟪x, w⟫_ℝ)⁻¹ := by
        convert mul_le_mul_of_nonneg_right h₂ t₂_nonneg using 1
        · rw [zero_mul]
        · rw [add_mul, mul_inv_cancel₀ H]
      let t₁ : {t : ℝ // 0 ≤ t} := ⟨_, t₁_nonneg⟩
      let t₂ : {t : ℝ // 0 ≤ t} := ⟨_, t₂_nonneg⟩
      -- With the above definitions, a computation shows that `v = t₁ • x + t₂ • y`.
      have v_eq : v = t₁ • x + t₂ • u := by rw [Nonneg.mk_smul, Nonneg.mk_smul, add_smul,
        smul_sub, smul_smul, inv_mul_cancel₀ H, smul_smul, mul_comm, add_add_sub_cancel,
        one_smul, one_smul, hv]
      rw [v_eq]
      -- But both `x` and `u` are in the span and `t₁` and `t₂` are nonnegativedd hence
      -- we are done.
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ x_mem) (Submodule.smul_mem _ _ u_mem)

lemma IsPolyhedral.inf_dual'_singleton {c : PointedCone ℝ E} (hc : c.IsPolyhedral) :
    IsPolyhedral (c ⊓ dual' {w}) := by
  obtain ⟨S, rfl⟩ := hc; exact ⟨infDualSingletonGenSet S w, span_infDualSingletonGenSet _ _⟩

/-- The dual of a polyhedral cone is polyhedral. -/
lemma IsPolyhedral.dual [FiniteDimensional ℝ E] {c : PointedCone ℝ E} (hc : c.IsPolyhedral) :
    c.dual.IsPolyhedral := by
  classical
  obtain ⟨S, rfl⟩ := hc
  rw [dual_span]
  induction' S using Finset.induction with x S hx hS
  · simp
  · rw [Finset.insert_eq, Finset.coe_union, dual'_union, inf_comm, Finset.coe_singleton]
    exact hS.inf_dual'_singleton

end NormedAddCommGroup
end PointedCone
