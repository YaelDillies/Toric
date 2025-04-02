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

open Classical

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

variable {𝕜 E : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- `⊤` is a polyhedral cone in a finite dimensional vector space over a linear
ordered field. -/
theorem IsPolyhedral.top [hE : FiniteDimensional 𝕜 E] :
    (⊤ : PointedCone 𝕜 E).IsPolyhedral := by
  obtain ⟨S,hS⟩ := Module.finite_def.mp hE
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
        obtain ⟨y,hy1,rfl⟩ := hx₂
        rw [neg_neg]
        exact Finset.mem_union_left _ hy1
    -- The three other cases in the induction are trivial
    · rw [neg_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [neg_add_rev]
      exact Submodule.add_mem _ hy hx
    · intro t x _ hx
      rw [←smul_neg]
      exact Submodule.smul_mem _ _ hx
  -- We now claim that `⊤` is generated as a pointed cone by `R`.
  use R
  symm
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
    · exact Submodule.smul_mem _ ⟨t,ht⟩ hx
    · rw [←neg_neg (t • x), ←neg_smul, ←smul_neg]
      apply Submodule.smul_mem _ (⟨-t, by linarith⟩ : {a : 𝕜 // 0 ≤ a})
      -- We use our auxiliary statement from above
      exact neg_mem_span_R _ hx
end

end PointedCone
