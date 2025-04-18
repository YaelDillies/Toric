import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Cone.Pointed
import Toric.Mathlib.Analysis.Convex.Extreme
import Toric.Mathlib.Analysis.Convex.Hull

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

section LinearOrderedField

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

theorem coe_span_eq_convexHull_of_smul_mem {s : Set E} (hn : s.Nonempty)
    (h : ∀ x ∈ s, ∀ a : 𝕜, a ≥ 0 → a • x ∈ s) :
    span 𝕜 s = convexHull 𝕜 s := by
  obtain ⟨x, hx⟩ := hn
  apply subset_antisymm
  · apply Submodule.span_induction
    · exact subset_convexHull 𝕜 s
    · apply subset_convexHull 𝕜 s
      simpa using h x hx 0
    · intro y z _ _ hy hz
      have hy₂ := smul_mem_convexHull h y hy 2 (by positivity)
      have hz₂ := smul_mem_convexHull h z hz 2 (by positivity)
      simpa using convex_convexHull 𝕜 s hy₂ hz₂ (a := 1 / 2) (b := 1 / 2)
        (by positivity) (by positivity) (by ring)
    · intro a x _ hx
      exact smul_mem_convexHull h x hx a.1 a.2
  · intro y hy
    apply mem_convexHull_iff.mp hy
    · exact subset_span
    · exact (span 𝕜 s).toConvexCone.convex

theorem coe_span_eq_convexHull {s : Set E} (hn : s.Nonempty) :
    span 𝕜 s = convexHull 𝕜 { x | ∃ (r : { r : 𝕜 // 0 ≤ r }) (y : E), y ∈ s ∧ x = r • y } := by
  let t := { x | ∃ (r : { r : 𝕜 // 0 ≤ r }) (y : E), y ∈ s ∧ x = r • y }
  rw [← coe_span_eq_convexHull_of_smul_mem]
  · simp only [SetLike.coe_set_eq]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      apply subset_span
      exact ⟨⟨1, by positivity⟩, x, hx, by simp⟩
    · rw [Submodule.span_le]
      rintro x ⟨r, x, hx, rfl⟩
      apply Submodule.smul_mem
      apply subset_span hx
  · obtain ⟨x, hx⟩ := hn
    exact ⟨x, 1, x, hx, by simp⟩
  · simp only [Subtype.exists, Nonneg.mk_smul]
    rintro x ⟨r, hr, y, hy, rfl⟩
    intro r' hr'
    rw [smul_smul]
    refine ⟨r' * r, by positivity, y, hy, rfl⟩

theorem mem_span_iff_mem_convexHull {s : Set E} (hn : s.Nonempty) {x : E} :
    x ∈ span 𝕜 s ↔
      x ∈ convexHull 𝕜 { x | ∃ (r : { r : 𝕜 // 0 ≤ r }) (y : E), y ∈ s ∧ x = r • y } := by
  rw [← coe_span_eq_convexHull hn]
  rfl

private theorem smul_mem_of_isExtreme.aux {a b c : 𝕜} {x : E} (hab : a < b) (hbc : b < c) :
    b • x ∈ openSegment 𝕜 (a • x) (c • x) := by
  have hba : b - a > 0 := by simp_all
  have hcb : c - b > 0 := by simp_all
  have hca : c - a > 0 := by simpa using add_pos hba hcb
  refine ⟨(c - b) / (c - a), (b - a) / (c - a), by positivity, by positivity, ?_, ?_⟩
  · rw [← add_div, sub_add_sub_cancel, div_self]
    positivity
  · simp only [smul_smul, smul_smul, ← add_smul, mul_comm, mul_div, ← add_div]
    congr
    rw [div_eq_iff (by positivity)]
    ring

theorem smul_mem_of_isExtreme {c : PointedCone 𝕜 E} {s : Set E} (he : IsExtreme 𝕜 c s) :
    ∀ x ∈ s, ∀ a : 𝕜, a ≥ 0 → a • x ∈ s := by
  intro x hxs a ha
  by_cases hcmp : a ≤ 1
  · by_cases a = 1 <;> (try simp_all; done)
    refine he.2 (c.smul_mem ⟨a, ha⟩ (he.1 hxs))
      (c.smul_mem ⟨2, by positivity⟩ (he.1 hxs)) hxs ?_ |>.1
    simpa using smul_mem_of_isExtreme.aux (𝕜 := 𝕜) (E := E) (b := 1)
      (lt_of_le_of_ne hcmp ‹_›) (by simp)
  · refine he.2 (c.smul_mem ⟨0, le_rfl⟩ (he.1 hxs)) (c.smul_mem ⟨a, ha⟩ (he.1 hxs)) hxs ?_ |>.2
    simpa using smul_mem_of_isExtreme.aux (𝕜 := 𝕜) (E := E) (a := 0) (b := 1)
      (by simp) (by simp_all)

theorem mem_span_inter_of_mem_span_of_isExtreme (c : PointedCone 𝕜 E)
    {t : Set E} (h : ∀ r : { r : 𝕜 // 0 ≤ r }, ∀ x ∈ t, r • x ∈ t) (he : IsExtreme 𝕜 c t) :
    t ⊆ c ∧ ∀ g : Set E, g ⊆ c → ∀ x ∈ span 𝕜 g, x ∈ t → x ∈ span 𝕜 (g ∩ t) := by
  have := smul_mem_of_isExtreme he
  simp only [isExtreme_iff_mem_convexHull_inter_of_mem_convexHull c t c.toConvexCone.convex] at he
  refine ⟨he.1, ?_⟩
  intro g hgc x hxg hxt
  by_cases hg : g.Nonempty
  · rw [mem_span_iff_mem_convexHull hg] at hxg
    let g' := { x : E | ∃ r : { r : 𝕜 // 0 ≤ r }, ∃ y ∈ g, x = r • y }
    replace he' := he.2 g' ?_ x hxg hxt
    · have : g' ∩ t ⊆ { x : E | x = 0 ∨ ∃ r : { r : 𝕜 // 0 ≤ r }, ∃ y ∈ g ∩ t, x = r • y } := by
        rintro _ ⟨⟨r, y, hyg, rfl⟩, hxt⟩
        by_cases hr : r = 0
        · simp_all
        · refine Or.inr ⟨r, y, ⟨hyg, ?_⟩, rfl⟩
          specialize h (1 / r) _ hxt
          obtain ⟨r, hr⟩ := r
          simp only [one_div, Nonneg.inv_mk, Nonneg.mk_smul] at h
          rwa [inv_smul_smul₀] at h
          intro h
          apply hr
          ext
          exact h
      replace he' := convexHull_mono this he'
      by_cases h' : (g ∩ t).Nonempty
      · rw [mem_span_iff_mem_convexHull h']
        convert he'
        simp only [Set.mem_inter_iff, Subtype.exists, Nonneg.mk_smul, exists_prop, iff_or_self]
        intro h
        obtain ⟨y, ⟨hyg, hyt⟩⟩ := h'
        exact ⟨0, le_rfl, y, ⟨hyg, hyt⟩, by simp [h]⟩
      · simp only [Set.not_nonempty_iff_eq_empty] at h'
        simpa [h'] using he'
    · rintro _ ⟨r, y, hyg, rfl⟩
      apply Submodule.smul_mem
      exact hgc hyg
  · simp_all [Set.not_nonempty_iff_eq_empty]

theorem span_eq_of_isExtreme_of_convex {c : PointedCone 𝕜 E} {s : Set E} (hn : s.Nonempty)
    (he : IsExtreme 𝕜 c s) (hc : Convex 𝕜 s) :
    span 𝕜 s = s := by
  apply le_antisymm
  · apply Submodule.span_induction
    · exact fun _ h => h
    · obtain ⟨x, hx⟩ := hn
      simpa using smul_mem_of_isExtreme he x hx 0
    · intro x y hx hy hxs hys
      have hx₂ : (2 : 𝕜) • x ∈ s := smul_mem_of_isExtreme he x hxs (a := 2) (by positivity)
      have hy₂ : (2 : 𝕜) • y ∈ s := smul_mem_of_isExtreme he y hys (a := 2) (by positivity)
      have := hc hx₂ hy₂ (a := 1 / 2) (b := 1 / 2) (by positivity) (by positivity) (by ring)
      simpa [smul_smul] using this
    · intro a y _ hys
      exact smul_mem_of_isExtreme he y hys a.1 a.2
  · exact Submodule.subset_span

theorem span_eq_of_isExposed [TopologicalSpace 𝕜] [TopologicalSpace E] {c : PointedCone 𝕜 E}
    {s : Set E} (hn : s.Nonempty) (he : IsExposed 𝕜 c s) :
    span 𝕜 s = s :=
  c.span_eq_of_isExtreme_of_convex hn he.isExtreme (he.convex c.toConvexCone.convex)

end LinearOrderedField
end PointedCone
