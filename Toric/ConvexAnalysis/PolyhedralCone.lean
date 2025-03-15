/-
Copyright (c) 2025 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
import Mathlib

/-!
# Polyhedral cones

TODO
-/

open scoped Pointwise

variable {R E : Type*} [OrderedSemiring R]

section

variable {𝕜 : Type u_1} {E : Type u_2} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable (𝕜)

def ConvexCone.ofGenerator (S : Set E) : ConvexCone 𝕜 E :=
  (convex_convexHull 𝕜 S).toCone

theorem subset_generatedCone (S : Set E) : S ⊆ ConvexCone.ofGenerator 𝕜 S :=
  (subset_convexHull 𝕜 S).trans (Convex.subset_toCone _)

def coneHull : ClosureOperator (Set E) := by
  apply ClosureOperator.mk₂ (α := Set E) (ConvexCone.ofGenerator 𝕜 ·)
  · exact subset_generatedCone 𝕜
  · intro _ _ h
    apply (convex_convexHull 𝕜 _).toCone_isLeast.2
    exact (ConvexCone.convex _).convexHull_subset_iff.mpr h

@[simp]
theorem ConvexCone.coe_ofGenerator (S : Set E) :
    (ConvexCone.ofGenerator 𝕜 S : Set E) = coneHull 𝕜 S :=
  rfl

@[simp]
theorem coneHull_isClosed (S : Set E) : (coneHull 𝕜).IsClosed S ↔
    Convex 𝕜 S ∧ ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ S → c • x ∈ S := by
  simp only [coneHull, ClosureOperator.mk₂_isClosed]
  apply Iff.intro
  · intro h
    rw [← h]
    refine ⟨ConvexCone.convex _, ConvexCone.smul_mem' _⟩
  · rintro ⟨hc, hm⟩
    apply subset_antisymm
    · rw [ConvexCone.ofGenerator]
      simp only [hc.convexHull_eq]
      let Sc : ConvexCone 𝕜 E := by
        refine ⟨S, hm, fun {x} hx {y} hy => ?_⟩
        suffices h : (1 / 2 : 𝕜) • x + (1 / 2 : 𝕜) • y ∈ S by
          simpa using hm (c := 2) (by positivity) h
        apply convex_iff_forall_pos.mp hc hx hy (by positivity) (by positivity) (by ring)
      have hSc : S ⊆ Sc := subset_rfl
      exact (Convex.toCone_isLeast (𝕜 := 𝕜) (E := E) (s := S) ?_).2 hSc
    · apply subset_generatedCone

theorem pointed_generatedCone {S : Set E} (h : 0 ∈ S) : (ConvexCone.ofGenerator 𝕜 S).Pointed :=
  subset_generatedCone 𝕜 S h

def PointedCone.ofGenerator (S : Set E) : PointedCone 𝕜 E := by
  apply ConvexCone.ofGenerator 𝕜 (S ∪ {0}) |>.toPointedCone
  apply pointed_generatedCone
  simp

theorem subset_generatedPointedCone (S : Set E) : S ⊆ PointedCone.ofGenerator 𝕜 S := by
  exact fun _ h => subset_generatedCone 𝕜 _ (by simp [h])

def pointedConeHull : ClosureOperator (Set E) := by
  apply ClosureOperator.mk₂ (α := Set E) (PointedCone.ofGenerator 𝕜 ·)
  · exact subset_generatedPointedCone 𝕜
  · intro S T h x
    simp [PointedCone.ofGenerator] at *
    apply ((coneHull 𝕜).le_closure_iff).mp
    rw [Set.le_iff_subset, Set.insert_subset_iff]
    refine ⟨?_, h⟩
    apply subset_generatedCone
    simp only [Set.mem_insert_iff, true_or]

@[simp]
theorem pointedConeHull_isClosed (S : Set E) : (coneHull 𝕜).IsClosed S ↔
    Convex 𝕜 S ∧ 0 ∈ S ∧ ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ S → c • x ∈ S := by
  simp only [coneHull, ClosureOperator.mk₂_isClosed]

def pointedConeHull_eq_coneHull_insert (S : Set E) :
    pointedConeHull 𝕜 S = coneHull 𝕜 (S.insert 0) := by
  simp only [coneHull, pointedConeHull, PointedCone.ofGenerator, Set.union_singleton]
  rfl

-- /-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
-- @[simps! isClosed]
-- def coneHull : ClosureOperator (Set E) := .ofCompletePred (Convex 𝕜) fun _ ↦ convex_sInter

/-- A set is a polytope if it is the convex hull of finitely many points. -/
def PointedCone.IsPolyhedral (c : PointedCone 𝕜 E) : Prop :=
  ∃ t : Finset E, c = PointedCone.ofGenerator 𝕜 t

end
