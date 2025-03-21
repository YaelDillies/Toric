/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Analysis.Convex.Cone.Pointed

/-!
# Polyhedral Cone

We define a polyhedral cone as the cone hull of finite set.

-/

namespace PointedCone

variable {𝕜 E : Type*} [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

variable (𝕜) in
/--
A cone is polyhedral iff it can be written
as the cone hull of a finite set.
-/
def IsPolyhedral (S : PointedCone 𝕜 E) : Prop :=
  ∃ t : Finset E, S = Submodule.span {c : 𝕜 // 0 ≤ c} t

@[simp] protected lemma IsPolyhedral.empty : IsPolyhedral 𝕜 (0 : PointedCone 𝕜 E) := ⟨∅, by simp⟩

end PointedCone
