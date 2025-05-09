import Mathlib.Analysis.Convex.Hull

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem smul_mem_convexHull {s : Set E} (h : ∀ x ∈ s, ∀ a : 𝕜, a ≥ 0 → a • x ∈ s) :
    ∀ x ∈ convexHull 𝕜 s, ∀ a : 𝕜, a ≥ 0 → a • x ∈ convexHull 𝕜 s := by
  intro x hx a ha
  have := Set.smul_mem_smul_set (a := a) hx
  rw [← convexHull_smul] at this
  refine convexHull_mono ?_ this
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy a ha
