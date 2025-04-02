/-
Copyright (c) 2025 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Mathlib.Analysis.Convex.Cone.Pointed

/-!
# Pointed cone hull and polyhedral cones

We define the pointed cone hull and what it means for a pointed cone to be polyhedral.
-/

variable {𝕜 E : Type*} [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

namespace PointedCone

variable (𝕜) in
/-- The span of a set `S` is the smallest pointed cone that contains `S`.
Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
submodule span of `S` w.r.t. nonnegative scalars. -/
abbrev span (S : Set E) : PointedCone 𝕜 E :=
  Submodule.span _ S

theorem subset_span {S : Set E} :
    S ⊆ PointedCone.span 𝕜 S :=
  Submodule.subset_span

/-- A pointed cone is polyhedral if it is the convex hull of finitely many points. -/
def IsPolyhedral (c : PointedCone 𝕜 E) : Prop :=
  ∃ t : Finset E, c = PointedCone.span 𝕜 t

protected def IsPolyhedral.span {s : Set E} (h : s.Finite) :
    (span 𝕜 s).IsPolyhedral :=
  ⟨h.toFinset, by simp⟩

@[simp]
theorem IsPolyhedral.bot :
    (⊥ : PointedCone 𝕜 E).IsPolyhedral :=
  ⟨{0}, by simp⟩

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical

theorem IsPolyhedral.top [hE : FiniteDimensional ℝ E] :
    (⊤ : PointedCone ℝ E).IsPolyhedral := by
  obtain ⟨S,hS⟩ := Module.finite_def.mp hE
  let R : Finset E := S ∪ S.map (Function.Embedding.mk (Neg.neg : E → E) neg_injective)
  have useful : ∀ x ∈ span ℝ R, (-x : E) ∈ span ℝ R := by
    apply Submodule.span_induction
    · intro x hx
      apply Submodule.subset_span
      rw [Finset.mem_coe, Finset.mem_union] at hx
      cases' hx with hx₁ hx₂
      · apply Finset.mem_union_right
        erw [Finset.mem_map']
        exact hx₁
      · rw [Finset.mem_map] at hx₂
        obtain ⟨y,hy1,rfl⟩ := hx₂
        apply Finset.mem_union_left
        rw [Function.Embedding.coeFn_mk, neg_neg]
        exact hy1
    · rw [neg_zero]
      exact Submodule.zero_mem _
    · intro x y hx1 hy1 hx2 hy2
      rw [neg_add_rev]
      exact Submodule.add_mem _ hy2 hx2
    · intro t x hx1 hx2
      rw [←smul_neg]
      exact Submodule.smul_mem _ _ hx2
  use R
  symm
  rw [Submodule.eq_top_iff']
  rw [Submodule.eq_top_iff'] at hS
  intro x
  specialize hS x
  revert hS x
  apply Submodule.span_induction
  · intro x hxS
    apply Submodule.subset_span
    exact Finset.mem_union_left _ hxS
  · apply Submodule.zero_mem
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro t x _ hx
    by_cases ht : 0 ≤ t
    · exact Submodule.smul_mem _ ⟨t,ht⟩ hx
    · rw [←neg_neg (t • x), ←neg_smul, ←smul_neg]
      apply Submodule.smul_mem _ (⟨-t, by linarith⟩ : {a : ℝ // 0 ≤ a})
      apply useful 
      exact hx
end

end PointedCone
