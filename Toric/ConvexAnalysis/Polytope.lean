/-
Copyright (c) 2025 Matthew Johnson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Johnson, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Hull

/-!
# Polytopes

We define polytopes as convex hulls of finite sets.
-/

open scoped Pointwise

variable {R E : Type*} [OrderedSemiring R]

section AddCommMonoid
variable [AddCommMonoid E] [Module R E] {s t : Set E} {x y : E}

variable (R) in
/-- A set is a polytope if it is the convex hull of finitely many points. -/
def IsPolytope (s : Set E) : Prop := ∃ t : Finset E, s = convexHull R t

@[simp] protected lemma IsPolytope.empty : IsPolytope R (∅ : Set E) := ⟨∅, by simp⟩
@[simp] protected lemma IsPolytope.singleton : IsPolytope R {x} := ⟨{x}, by simp⟩

@[simp] protected lemma IsPolytope.segment : IsPolytope R <| segment R x y := by
  classical exact ⟨{x, y}, by simp⟩

@[simp]
lemma IsPolytope.convexHull_Finset {s : Finset E} : IsPolytope R <| convexHull R s.toSet := by use s

protected lemma IsPolytope.add (hs : IsPolytope R s) (ht : IsPolytope R t) :
    IsPolytope R (s + t) := by sorry

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup E] [Module R E] {s t : Set E} {x y : E}

protected lemma IsPolytope.neg (hs : IsPolytope R s) : IsPolytope R (-s) := by sorry

protected lemma IsPolytope.sub (hs : IsPolytope R s) (ht : IsPolytope R t) :
    IsPolytope R (s - t) := by sorry

end AddCommGroup
