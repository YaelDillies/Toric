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
    (hS : ∀ x ∈ S, 0 < ⟪x, w⟫_ℝ) (h : x ∈ span ℝ S) (hw : ⟪x, w⟫_ℝ = 0) : x = 0 := by
  induction h using Submodule.span_induction with
  | mem x h => exact False.elim <| ne_of_lt (hS x h) hw.symm
  | zero => rfl
  | add x y hx hy hxw hyw =>
    rw [inner_add_left] at hw
    have H : ⟪x, w⟫_ℝ = 0 ∧ ⟪y,w⟫_ℝ = 0 := (add_eq_zero_iff_of_nonneg
      (inner_nonneg_of_mem_span_inner_nonneg (fun z hz => (hS z hz).le) hx)
      (inner_nonneg_of_mem_span_inner_nonneg (fun z hz => (hS z hz).le) hy)).mp hw
    rw [hxw H.1, hyw H.2]
    exact zero_add 0
  | smul t x hx hxw =>
    rw [smul_eq_zero]
    rw [Nonneg.mk_smul, real_inner_smul_left, mul_eq_zero, NNReal.val_eq_coe,
      NNReal.coe_eq_zero] at hw
    exact Or.elim hw Or.inl (fun h => Or.inr (hxw h))

lemma eq_zero_of_inner_eq_zero_of_mem_span_inner_neg (w : E) (S : Set E)
    (hS : ∀ x ∈ S, ⟪x, w⟫_ℝ < 0) {x : E} (h : x ∈ span ℝ S) (hw : ⟪x, w⟫_ℝ = 0) : x = 0 := by
  induction h using Submodule.span_induction with
  | mem x h => exact False.elim <| ne_of_lt (hS x h) hw
  | zero => rfl
  | add x y hx hy hxw hyw =>
    rw [inner_add_left] at hw
    have H := (add_eq_zero_iff_of_nonneg
      (neg_nonneg_of_nonpos <|
        inner_nonpos_of_mem_span_inner_nonpos (fun z hz => (hS z hz).le) hx)
      (neg_nonneg_of_nonpos <|
        inner_nonpos_of_mem_span_inner_nonpos (fun z hz => (hS z hz).le) hy)).mp <| by
      rw [←neg_add, hw, neg_zero]
    rw [neg_eq_zero, neg_eq_zero] at H
    rw [hxw H.1, hyw H.2]
    exact zero_add 0
  | smul t x hx hxw =>
    rw [smul_eq_zero]
    rw [Nonneg.mk_smul, real_inner_smul_left, mul_eq_zero, NNReal.val_eq_coe,
      NNReal.coe_eq_zero] at hw
    exact Or.elim hw Or.inl (fun h => Or.inr (hxw h))

end NormedAddCommGroup
end PointedCone
