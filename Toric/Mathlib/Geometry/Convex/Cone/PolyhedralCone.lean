/-
Copyright (c) 2025 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Toric.Mathlib.Geometry.Convex.Cone.Dual
import Toric.Mathlib.Algebra.Order.Nonneg.Module



namespace PointedCone

open Submodule hiding span

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

variable (S : Set M) (w : N)

variable (p) in
/-- A generating set for `dual p S ⊔ span R {w}`, see `dual_sup_span_singleton_eq_dual -/
private noncomputable abbrev dualSupSingletonGenSet : Set M :=
  {s ∈ S | 0 ≤ p s w} ∪
    .image2 (fun x y => p x w • y - p y w • x) {s ∈ S | 0 ≤ p s w} {s ∈ S | p s w ≤ 0}

private lemma dualSupSingletonGenSet_subset_span :
    (dualSupSingletonGenSet p S w : Set M) ⊆ span R S := by
  rw [Set.union_subset_iff]
  use subset_trans (fun x hx => hx.1) subset_span
  simp only [Set.image2_subset_iff, Set.mem_setOf_eq, SetLike.mem_coe, and_imp]
  intro x hxS hxw y hyS hyw
  convert add_mem (smul_mem (span R S) ⟨p x w, hxw⟩ (subset_span hyS))
    (smul_mem _ ⟨-p y w, neg_nonneg.mpr hyw⟩ (subset_span hxS)) using 1
  rw [sub_eq_add_neg, Nonneg.mk_smul, Nonneg.mk_smul, neg_smul]

private lemma span_singleton_le_dualSupSingletonGenSet :
    span R {w} ≤ dual' p (dualSupSingletonGenSet p S w) := by
  rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_dual']
  rintro z (hz | hz)
  · exact hz.2
  · simp only [Set.mem_image2, Set.mem_setOf_eq] at hz
    obtain ⟨x, ⟨hxS, hxw⟩, y, ⟨hyS, hyw⟩, rfl⟩ := hz
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      sub_nonneg]
    rw [mul_comm]

private lemma dual_sup_span_singleton_eq_dual :
    dual' p S ⊔ span R {w} = dual' p (dualSupSingletonGenSet p S w) := by
  apply le_antisymm
  · rw [←dual_span]
    exact sup_le (dual_le_dual (dualSupSingletonGenSet_subset_span S w))
      (span_singleton_le_dualSupSingletonGenSet S w)
  · sorry

end LinearOrder

end PointedCone
