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

variable {𝕜 : Type*} {E : Type*} [OrderedSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable (𝕜) in
def PointedCone.ofGenerators (S : Set E) : PointedCone 𝕜 E :=
  Submodule.span _ S

theorem PointedCone.subset_ofGenerators {S : Set E} :
    S ⊆ PointedCone.ofGenerators 𝕜 S :=
  Submodule.subset_span

/-- A pointed cone is polyhedral if it is the convex hull of finitely many points. -/
def PointedCone.IsPolyhedral (c : PointedCone 𝕜 E) : Prop :=
  ∃ t : Finset E, c = PointedCone.ofGenerators 𝕜 t

@[simp]
theorem PointedCone.IsPolyhedral.bot :
    (⊥ : PointedCone 𝕜 E).IsPolyhedral := by
  refine ⟨{0}, ?_⟩
  ext
  simp [ofGenerators]
