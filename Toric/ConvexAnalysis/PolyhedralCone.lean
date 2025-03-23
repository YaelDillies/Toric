/-
Copyright (c) 2025 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Mathlib

/-!
# Cone hull and pointed cone hull

We define the (pointed) cone hull and what it means for a pointed cone to be polyhedral.
-/

open scoped Pointwise

variable {𝕜 E : Type*} [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

variable (𝕜) in
/-- The span of a set `S` is the smallest pointed cone that contains `S`.
Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
submodule span of `S` w.r.t. nonnegative scalars. -/
def PointedCone.span (S : Set E) : PointedCone 𝕜 E :=
  Submodule.span _ S

theorem PointedCone.subset_span {S : Set E} :
    S ⊆ PointedCone.span 𝕜 S :=
  Submodule.subset_span

theorem PointedCone.span_eq_submoduleSpan {S : Set E} :
    PointedCone.span 𝕜 S = Submodule.span _ S := rfl

/-- A pointed cone is polyhedral if it is the convex hull of finitely many points. -/
def PointedCone.IsPolyhedral (c : PointedCone 𝕜 E) : Prop :=
  ∃ t : Finset E, c = PointedCone.span 𝕜 t

def PointedCone.isPolyhedral_def {c : PointedCone 𝕜 E} :
    c.IsPolyhedral ↔ ∃ s : Finset E, c = PointedCone.span 𝕜 s :=
  Iff.rfl

def PointedCone.isPolyhedral_span (s : Set E) [Fintype s] :
    (PointedCone.span 𝕜 s).IsPolyhedral :=
  ⟨s.toFinset, by simp⟩

@[simp]
theorem PointedCone.IsPolyhedral.bot :
    (⊥ : PointedCone 𝕜 E).IsPolyhedral := by
  refine ⟨{0}, ?_⟩
  ext
  simp [span]
