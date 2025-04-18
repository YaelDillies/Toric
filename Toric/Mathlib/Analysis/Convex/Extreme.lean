import Mathlib.Analysis.Convex.Extreme


variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

theorem isExtreme_iff_mem_convexHull_inter_of_mem_convexHull (s t : Set E) (hc : Convex 𝕜 s) :
    IsExtreme 𝕜 s t ↔
      t ⊆ s ∧ ∀ g : Set E, g ⊆ s → ∀ x ∈ convexHull 𝕜 g, x ∈ t → x ∈ convexHull 𝕜 (g ∩ t) := by
  constructor
  · intro he
    refine ⟨he.1, ?_⟩
    intro g hgs
    have hcgs := hc.convexHull_subset_iff.mpr hgs
    let s' := { x ∈ convexHull 𝕜 g | x ∈ t → x ∈ convexHull 𝕜 (g ∩ t) }
    have hcs' : Convex 𝕜 s' := by
      intro x hx y hy a b ha hb hab
      refine ⟨convex_convexHull 𝕜 _ hx.1 hy.1 ha hb hab, ?_⟩
      intro ht
      by_cases h : a > 0 ∧ b > 0
      · have := he.2 (hcgs hx.1) (hcgs hy.1) ht ?_
        · exact convex_convexHull 𝕜 _ (hx.2 this.1) (hy.2 this.2) ha hb hab
        · exact ⟨a, b, h.1, h.2, hab, rfl⟩
      · simp only [not_and_or] at h
        cases h
        · have : a = 0 := le_antisymm (le_of_not_gt ‹_›) ha
          simp_all only [le_refl, zero_add, zero_smul, one_smul, gt_iff_lt, lt_self_iff_false,
            not_false_eq_true, zero_le_one]
          exact hy.2 ht
        · have : b = 0 := le_antisymm (le_of_not_gt ‹_›) hb
          simp_all only [le_refl, add_zero, one_smul, zero_smul, gt_iff_lt, lt_self_iff_false,
            not_false_eq_true, zero_le_one]
          exact hx.2 ht
    intro x hx
    rw [mem_convexHull_iff] at hx
    refine hx s' ?_ hcs' |>.2
    exact fun y hyg => ⟨subset_convexHull 𝕜 _ hyg, fun hyt => subset_convexHull 𝕜 _ ⟨hyg, hyt⟩⟩
  · intro h
    constructor
    · exact h.1
    · rintro x hx y hy _ hzt ⟨a, b, ha, hb, hab, rfl⟩
      replace h := h.2 {x, y} ?_ _ ?_ hzt
      · by_cases hxt : x ∈ t
        · by_cases hyt : y ∈ t
          · exact ⟨hxt, hyt⟩
          · rw [Set.insert_inter_of_mem hxt, Set.singleton_inter_eq_empty.mpr hyt] at h
            simp at h
            replace h : y = x := by
              rw [← eq_sub_iff_add_eq'] at h
              rw (occs := [1]) [← one_smul 𝕜 x] at h
              rw [← sub_smul, ← hab, add_sub_cancel_left] at h
              replace h := congr_arg (b⁻¹ • ·) h
              simpa [inv_smul_smul₀ (ne_of_gt hb)] using h
            exact ⟨hxt, h ▸ hxt⟩
        · by_cases hyt : y ∈ t
          · rw [Set.insert_inter_of_not_mem hxt] at h
            replace h := convexHull_mono Set.inter_subset_left h
            simp only [convexHull_singleton, Set.mem_singleton_iff] at h
            replace h : x = y := by
              rw [← eq_sub_iff_add_eq] at h
              rw (occs := [1]) [← one_smul 𝕜 y] at h
              rw [← sub_smul, ← hab, add_sub_cancel_right] at h
              replace h := congr_arg (a⁻¹ • ·) h
              simpa [inv_smul_smul₀ (ne_of_gt ha)] using h
            exact ⟨h ▸ hyt, hyt⟩
          · rw [Set.insert_inter_of_not_mem hxt, Set.singleton_inter_eq_empty.mpr hyt] at h
            simp at h
      · rintro a (hax | hay)
        · exact hax ▸ hx
        · exact hay ▸ hy
      · exact convex_convexHull 𝕜 {x, y}
          (subset_convexHull 𝕜 _ (by simp)) (subset_convexHull 𝕜 _ (by simp))
          (a := a) (by positivity) (b := b) (by positivity) hab
