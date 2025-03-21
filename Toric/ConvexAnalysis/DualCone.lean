/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Analysis.Convex.Cone.Pointed

/-!
# Lemmas

Prove some lemmas about the dual cone.
-/

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s t : PointedCone ℝ E)

lemma PointedCone.dual_add : (s + t).dual = s.dual ⊓ t.dual := sorry
