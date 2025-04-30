/-
Copyright (c) 2025 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Toric.Mathlib.Geometry.Convex.Cone.Dual
import Toric.Mathlib.Algebra.Order.Nonneg.Module



namespace PointedCone

section PartialOrder

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
def IsPolyhedral (c : PointedCone R N) : Prop :=
  ∃ t : Finset M, c = dual' p t

theorem IsPolyhedral.dual {t : Set M} (h : t.Finite) :
    IsPolyhedral p (dual' p t) := ⟨h.toFinset, by simp⟩

theorem IsPolyhedral.top : IsPolyhedral p (⊤ : PointedCone R N) := ⟨∅, by simp⟩

@[simp]
theorem IsPolyhedral.dual_dual_flip {c : PointedCone R N} (hc : IsPolyhedral p c) :
    dual' p (dual' p.flip (c : Set N)) = c := by
  obtain ⟨t,rfl⟩ := hc
  exact dual_dual_dual_eq_dual

end PartialOrder

section LinearOrder

variable {R M N : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

theorem IsPolyhedral.bot [Module.Finite R M] (hp : Function.Injective p.flip) :
    IsPolyhedral p (⊥ : PointedCone R N) := by
  obtain ⟨S, hS : span R _ = ⊤⟩ := (Nonneg.isFiniteModuleOver R M).fg_top
  use S
  rw [← dual_span, hS, Submodule.top_coe, dual_univ hp, Submodule.zero_eq_bot]

end LinearOrder

section LinearOrderedField
