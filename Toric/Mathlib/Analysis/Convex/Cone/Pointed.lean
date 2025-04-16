import Mathlib.Analysis.Convex.Cone.Pointed

/-!
# TODO

Make cone explicit in `ConvexCone.toPointedCone`
-/

open scoped InnerProductSpace

namespace PointedCone
variable {𝕜 E : Type*}

section Module
variable [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  {S : Set E}

@[simp]
lemma _root_.ConvexCone.toPointedCone_top : (⊤ : ConvexCone 𝕜 E).toPointedCone trivial = ⊤ := rfl

variable (𝕜 S) in
/-- The span of a set `S` is the smallest pointed cone that contains `S`.

Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
submodule span of `S` w.r.t. nonnegative scalars. -/
abbrev span : PointedCone 𝕜 E := Submodule.span _ S

lemma subset_span : S ⊆ PointedCone.span 𝕜 S := Submodule.subset_span

end Module

section NormedAddCommGroup
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] {w x y : E} {s t : Set E}

-- TODO: Replace `dual`
variable (s) in
/-- The dual of an arbitrary set as a `PointedCone`. -/
def dual' : PointedCone ℝ E := s.innerDualCone.toPointedCone <| pointed_innerDualCone s

@[simp, norm_cast]
lemma toConvexCone_dual' (s : Set E) : ↑(dual' s) = (s : Set E).innerDualCone := rfl

lemma dual_eq_dual' (σ : PointedCone ℝ E) : σ.dual = dual' (σ : Set E) := rfl

@[simp] lemma mem_dual' : y ∈ dual' s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ ⟪x, y⟫_ℝ := .rfl

@[gcongr] lemma dual'_le_dual' (h : s ⊆ t) : dual' t ≤ dual' s := fun _ hx y hy => hx y (h hy)

@[simp] lemma dual'_empty : dual' (∅ : Set E) = ⊤ := by simp [dual']

lemma dual'_union (s t : Set E) : dual' (s ∪ t) = dual' s ⊓ dual' t := by
  refine le_antisymm (le_inf (dual'_le_dual' le_sup_left) (dual'_le_dual' le_sup_right)) ?_
  rintro x ⟨hxs, hxt⟩ y (hy | hy)
  exacts [hxs y hy, hxt y hy]

lemma dual_span (s : Set E) : (span ℝ s).dual = dual' s := by
  refine le_antisymm (innerDualCone_le_innerDualCone subset_span) ?_
  intro x hx
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

lemma inner_nonneg_of_mem_span_inner_nonneg (hs : ∀ x ∈ s, 0 ≤ ⟪x, w⟫_ℝ) (hx : x ∈ span ℝ s) :
    0 ≤ ⟪x, w⟫_ℝ := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs _ hx
  | zero => simp
  | add x y hx hy hxw hyw =>
    rw [inner_add_left]
    exact add_nonneg hxw hyw
  | smul t x hx hxw =>
    rw [Nonneg.mk_smul, real_inner_smul_left]
    exact mul_nonneg t.2 hxw

lemma inner_nonpos_of_mem_span_inner_nonpos (hs : ∀ x ∈ s, ⟪x, w⟫_ℝ ≤ 0) (hx : x ∈ span ℝ s) :
    ⟪x, w⟫_ℝ ≤ 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs _ hx
  | zero => simp
  | add x y hx hy hxw hyw =>
    rw [inner_add_left]
    exact add_nonpos hxw hyw
  | smul t x hx hxw =>
    rw [Nonneg.mk_smul, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos t.2 hxw

lemma eq_zero_of_inner_eq_zero_of_mem_span_inner_pos (hs : ∀ x ∈ s, 0 < ⟪x, w⟫_ℝ)
    (hx : x ∈ span ℝ s) (hw : ⟪x, w⟫_ℝ = 0) : x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x h => exact False.elim <| ne_of_lt (hs x h) hw.symm
  | zero => rfl
  | add x y hx hy hxw hyw =>
    rw [inner_add_left] at hw
    have H : ⟪x, w⟫_ℝ = 0 ∧ ⟪y,w⟫_ℝ = 0 := (add_eq_zero_iff_of_nonneg
      (inner_nonneg_of_mem_span_inner_nonneg (fun z hz => (hs z hz).le) hx)
      (inner_nonneg_of_mem_span_inner_nonneg (fun z hz => (hs z hz).le) hy)).mp hw
    rw [hxw H.1, hyw H.2]
    exact zero_add 0
  | smul t x hx hxw =>
    rw [smul_eq_zero]
    rw [Nonneg.mk_smul, real_inner_smul_left, mul_eq_zero, NNReal.val_eq_coe,
      NNReal.coe_eq_zero] at hw
    exact Or.elim hw Or.inl (fun h => Or.inr (hxw h))

lemma eq_zero_of_inner_eq_zero_of_mem_span_inner_neg (hs : ∀ x ∈ s, ⟪x, w⟫_ℝ < 0)
    (hx : x ∈ span ℝ s) (hw : ⟪x, w⟫_ℝ = 0) : x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x h => exact False.elim <| ne_of_lt (hs x h) hw
  | zero => rfl
  | add x y hx hy hxw hyw =>
    rw [inner_add_left] at hw
    have H := (add_eq_zero_iff_of_nonneg
      (neg_nonneg_of_nonpos <|
        inner_nonpos_of_mem_span_inner_nonpos (fun z hz => (hs z hz).le) hx)
      (neg_nonneg_of_nonpos <|
        inner_nonpos_of_mem_span_inner_nonpos (fun z hz => (hs z hz).le) hy)).mp <| by
      rw [←neg_add, hw, neg_zero]
    rw [neg_eq_zero, neg_eq_zero] at H
    rw [hxw H.1, hyw H.2]
    exact zero_add 0
  | smul t x hx hxw =>
    rw [smul_eq_zero]
    rw [Nonneg.mk_smul, real_inner_smul_left, mul_eq_zero, NNReal.val_eq_coe,
      NNReal.coe_eq_zero] at hw
    exact Or.elim hw .inl fun h => .inr (hxw h)

end NormedAddCommGroup
end PointedCone
