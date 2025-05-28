import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.RingTheory.Finiteness.Basic

namespace Nonneg

section Ring

variable (𝕜 E : Type*) [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E] [Module 𝕜 E]

local notation "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

private instance instModuleFiniteAux : Module.Finite 𝕜≥0 𝕜 := by
  simp_rw [Module.finite_def, Submodule.fg_def, Submodule.eq_top_iff']
  refine ⟨{1, -1}, by simp, fun x ↦ ?_⟩
  obtain hx | hx := le_total 0 x
  · simpa using Submodule.smul_mem (M := 𝕜) (.span 𝕜≥0 {1, -1}) ⟨x, hx⟩ (x := 1)
      (Submodule.subset_span <| by simp)
  · simpa using Submodule.smul_mem (M := 𝕜) (.span 𝕜≥0 {1, -1}) ⟨-x, neg_nonneg.2 hx⟩ (x := -1)
      (Submodule.subset_span <| by simp)

/-- If a module is finite over a linearly ordered ring, then it is also finite over the non-negative
scalars. -/
instance instModuleFinite [Module.Finite 𝕜 E] : Module.Finite 𝕜≥0 E := .trans 𝕜 E

end Ring

end Nonneg
