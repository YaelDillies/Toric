/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Analysis.Convex.Exposed

/-!
# Salient Cones

We prove some equivalent conditions for a cone to be salient.
-/

variable {E : Type*} [NormedAddCommGroup E] [TopologicalSpace E]
  [InnerProductSpace ℝ E] (S : PointedCone ℝ E)

theorem PointedCone.salient_tfae :
  [
    S.toConvexCone.Salient,
    IsExposed ℝ {0} S,
    ∀ (s : Submodule ℝ E), s.restrictScalars NNReal ≤ S → s = 0,
    ∀ (s : Submodule ℝ E), S.dual ≤ s.restrictScalars NNReal → S = ⊤
  ].TFAE := sorry
