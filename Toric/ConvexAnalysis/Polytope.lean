/-
Copyright (c) 2025 Matthew Johnson, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Johnson, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
/-!
# Polytopes

We define polytopes as convex hulls of finite sets.
-/

open scoped Pointwise

section AddCommMonoid
variable {R E : Type*} [OrderedSemiring R]
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

end AddCommMonoid

section AddCommGroup
variable {R E : Type*} [LinearOrderedField R]
variable [AddCommGroup E] [Module R E] {s t : Set E} {x y : E}

protected lemma IsPolytope.add (hs : IsPolytope R s) (ht : IsPolytope R t) :
    IsPolytope R (s + t) := by
    unfold IsPolytope
    rcases hs with ⟨A, hA⟩
    rcases ht with ⟨B, hB⟩
    classical
    rw [hB, hA]
    use ((↑A) + (↑B))
    simp
    rw [convexHull_add A.toSet B.toSet]


protected lemma IsPolytope.neg (hs : IsPolytope R s) :
    IsPolytope R (-s) := by
    unfold IsPolytope
    rcases hs with ⟨A, hA⟩
    classical
    rw [hA]
    use -A
    rw [← convexHull_neg A.toSet]
    simp


protected lemma IsPolytope.sub (hs : IsPolytope R s) (ht : IsPolytope R t) :
    IsPolytope R (s - t) := by
    unfold IsPolytope
    rcases hs with ⟨A, hA⟩
    rcases ht with ⟨B, hB⟩
    rw [hA, hB]
    classical
    use ((↑A) - (↑B))
    simp
    rw [convexHull_sub A.toSet B.toSet]

end AddCommGroup
