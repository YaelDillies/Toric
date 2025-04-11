import Mathlib.Analysis.Convex.Cone.Pointed
import Toric.Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# TODO

Make cone explicit in `ConvexCone.toPointedCone`
-/

--open scoped InnerProductSpace

namespace PointedCone
variable {𝕜 E : Type*}

section Module
variable [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] {S : Set E}

@[simp]
lemma _root_.ConvexCone.toPointedCone_top : (⊤ : ConvexCone 𝕜 E).toPointedCone trivial = ⊤ := rfl

variable (𝕜 S) in
/-- The span of a set `S` is the smallest pointed cone that contains `S`.

Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
submodule span of `S` w.r.t. nonnegative scalars. -/
abbrev span : PointedCone 𝕜 E := Submodule.span _ S

lemma subset_span : S ⊆ PointedCone.span 𝕜 S := Submodule.subset_span

end Module

section Dual

open scoped PerfectPairing

variable {𝕜 : Type*} {N M : Type*}
variable [OrderedCommRing 𝕜] [AddCommGroup N] [AddCommGroup M] [Module 𝕜 N] [Module 𝕜 M]
variable [PerfectPairing 𝕜 N M]

variable (𝕜 M) in
/-- The dual cone of a set as a pointed cone in the dual space. -/
def dual' (s : Set N) : PointedCone 𝕜 M where
  carrier := {y : M | ∀ x ∈ s, 0 ≤ ⟪x, y⟫_𝕜}
  add_mem' ha hb w hw := by
    rw [PerfectPairing.inner_add_right]
    exact add_nonneg (ha w hw) (hb w hw)
  zero_mem' w hw := by rw [PerfectPairing.inner_zero_right]
  smul_mem' t y hy w hw := by
    rw [Nonneg.mk_smul, PerfectPairing.inner_smul_right]
    exact mul_nonneg t.2 (hy w hw)

variable {x : N} {y : M} {s t : Set N}

@[simp] lemma mem_dual' : y ∈ dual' 𝕜 M s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ ⟪x, y⟫_𝕜 := .rfl

@[gcongr] lemma dual'_le_dual' (h : s ⊆ t) : dual' 𝕜 M t ≤ dual' 𝕜 M s :=
  fun _ hx y hy => hx y (h hy)

@[simp] lemma dual'_empty : dual' 𝕜 M (∅ : Set N) = ⊤ := by simp [dual']; rfl

lemma dual'_union : dual' 𝕜 M (s ∪ t) = dual' 𝕜 M s ⊓ dual' 𝕜 M t := by
  refine le_antisymm (le_inf (dual'_le_dual' le_sup_left) (dual'_le_dual' le_sup_right)) ?_
  rintro y ⟨hys, hyt⟩ x (hx | hx)
  exacts [hys x hx, hyt x hx]

@[simp]
lemma dual'_span : dual' 𝕜 M (span 𝕜 s : Set N) = dual' 𝕜 M s := by
  refine le_antisymm (dual'_le_dual' Submodule.subset_span) ?_
  intro x hx y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hx y hy
  | zero => simp
  | add y z hys hzs hyx hzx =>
    rw [PerfectPairing.inner_add_left]
    exact add_nonneg hyx hzx
  | smul t y hys hyx =>
    rw [Nonneg.mk_smul, PerfectPairing.inner_smul_left]
    exact mul_nonneg t.2 hyx

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

end Dual

end PointedCone
