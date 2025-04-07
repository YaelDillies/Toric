import Mathlib.Analysis.Convex.Cone.Pointed

open scoped InnerProductSpace

namespace PointedCone
variable {𝕜 E : Type*}

section Module
variable [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] {S : Set E}

variable (𝕜 S) in
/-- The span of a set `S` is the smallest pointed cone that contains `S`.

Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
submodule span of `S` w.r.t. nonnegative scalars. -/
abbrev span : PointedCone 𝕜 E := Submodule.span _ S

lemma subset_span : S ⊆ PointedCone.span 𝕜 S := Submodule.subset_span

end Module

section NormedAddCommGroup
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] {w x : E} {S : Set E}

lemma inner_nonneg_of_mem_span_inner_nonneg (hS : ∀ x ∈ S, 0 ≤ ⟪x, w⟫_ℝ) (hx : x ∈ span ℝ S) :
    0 ≤ ⟪x, w⟫_ℝ := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS _ hx
  | zero => simp
  | add x y hx hy hxw hyw =>
    rw [inner_add_left]
    exact add_nonneg hxw hyw
  | smul t x hx hxw =>
    rw [Nonneg.mk_smul, real_inner_smul_left]
    exact mul_nonneg t.2 hxw

lemma inner_nonpos_of_mem_span_inner_nonpos (hS : ∀ x ∈ S, ⟪x, w⟫_ℝ ≤ 0) (hx : x ∈ span ℝ S) :
    ⟪x, w⟫_ℝ ≤ 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS _ hx
  | zero => simp
  | add x y hx hy hxw hyw =>
    rw [inner_add_left]
    exact add_nonpos hxw hyw
  | smul t x hx hxw =>
    rw [Nonneg.mk_smul, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos t.2 hxw

lemma eq_zero_of_inner_eq_zero_of_mem_span_inner_pos
    (hS : ∀ x ∈ S, 0 < ⟪x, w⟫_ℝ) (hx₁ : x ∈ span ℝ S) (hx₂ : ⟪x, w⟫_ℝ = 0) : x = 0 := by
  revert x
  apply Submodule.span_induction
  · intro x hxS hxw
    specialize hS x hxS
    linarith
  · intro h
    rfl
  · intro x y hxS hyS hx hy hxyw
    rw [inner_add_left] at hxyw
    have H : ⟪x, w⟫_ℝ = 0 ∧ ⟪y,w⟫_ℝ = 0 := (add_eq_zero_iff_of_nonneg
      (inner_nonneg_of_mem_span_inner_nonneg (fun z hz => le_of_lt (hS z hz)) hxS)
      (inner_nonneg_of_mem_span_inner_nonneg (fun z hz => le_of_lt (hS z hz)) hyS)).mp hxyw
    rw [hx H.1, hy H.2]
    exact zero_add 0
  · intro ⟨t,ht⟩ x hxS hx hxw
    rw [Nonneg.mk_smul, real_inner_smul_left] at hxw
    rw [Nonneg.mk_smul]
    by_cases ht : t = 0
    · rw [ht, zero_smul]
    · rw [hx ((mul_eq_zero_iff_left ht).mp hxw), smul_zero]

lemma eq_zero_of_inner_eq_zero_of_mem_span_inner_neg (w : E) (S : Set E)
    (hS : ∀ x ∈ S, ⟪x, w⟫_ℝ < 0) {x : E} (hx₁ : x ∈ span ℝ S) (hx₂ : ⟪x, w⟫_ℝ = 0) : x = 0 := by
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
        inner_nonpos_of_mem_span_inner_nonpos (fun z hz => (hS z hz).le) hxS)
      (neg_nonneg_of_nonpos <|
        inner_nonpos_of_mem_span_inner_nonpos (fun z hz => (hS z hz).le) hyS)).mp <| by
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

end NormedAddCommGroup
end PointedCone
