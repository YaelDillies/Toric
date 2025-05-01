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

lemma IsPolyhedral_def {c : PointedCone R N} :
    IsPolyhedral p c ↔ ∃ t, t.Finite ∧ c = dual' p t :=
  ⟨fun ⟨t, ht⟩ => ⟨t, t.finite_toSet, ht⟩,
   fun ⟨_, ht1, ht2⟩ =>⟨ht1.toFinset, ht1.coe_toFinset.symm ▸ ht2⟩⟩

lemma IsPolyhedral_dual_of_Finite {t : Set M} (h : t.Finite) :
    IsPolyhedral p (dual' p t) := ⟨h.toFinset, by simp⟩

lemma IsPolyhedral_dual_of_FG {c : PointedCone R M} (hc : c.FG) :
    IsPolyhedral p (dual' p (c : Set M)) := by
  obtain ⟨S, rfl⟩ := hc
  rw [dual_span]
  exact ⟨S,rfl⟩ 

theorem IsPolyhedral_top : IsPolyhedral p (⊤ : PointedCone R N) := ⟨∅, by simp⟩

@[simp]
theorem IsPolyhedral_dual_dual {c : PointedCone R N} (hc : IsPolyhedral p c) :
    dual' p (dual' p.flip (c : Set N)) = c := by
  obtain ⟨t,rfl⟩ := hc
  exact dual_dual_dual_eq_dual

end PartialOrder

section LinearOrder

variable {R M N : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

theorem IsPolyhedral_bot [Module.Finite R M] (hp : Function.Injective p.flip) :
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
    span R {w} ⊔ dual' p S = dual' p (dualSupSingletonGenSet p S w) := by
  apply le_antisymm
  · rw [←dual_span]
    apply sup_le (span_singleton_le_dualSupSingletonGenSet S w)
    apply dual_le_dual
    exact dualSupSingletonGenSet_subset_span S w
  · rw [dual_union]
    intro x ⟨hx1, hx2⟩ 
    sorry

theorem IsPolyhedral_of_fg [Module.Finite R M] (hp : Function.Injective p.flip)
    {c : PointedCone R N} (hc : c.FG) : IsPolyhedral p c := by
  classical
  obtain ⟨S, rfl⟩ := hc
  induction S using Finset.induction with
  | empty =>
    rw [Finset.coe_empty, span_empty]
    exact IsPolyhedral_bot hp
  | @insert w A hwA hA =>
    simp
    rw [Submodule.span_insert]
    obtain ⟨S, hS⟩ := hA
    rw [hS, dual_sup_span_singleton_eq_dual]
    apply IsPolyhedral_dual_of_Finite
    rw [Set.finite_union]
    refine ⟨?_, Set.Finite.image2 _ ?_ ?_⟩ <;>
      exact Set.Finite.subset (S.finite_toSet) (fun x hx => hx.1)

lemma IsPolyhedral_span [Module.Finite R M] (hp : Function.Injective p.flip) {S : Set N}
    (hS : S.Finite) : IsPolyhedral p (span R S) :=
  IsPolyhedral_of_fg hp (fg_span hS)

lemma dual_dual_eq_span [Module.Finite R M] (hp : Function.Injective p.flip) {S : Set N}
    (hS : S.Finite) : dual' p (dual' p.flip S) = span R S := by
  nth_rw 2 [←dual_span]
  exact IsPolyhedral_dual_dual (IsPolyhedral_span hp hS)

theorem fg_of_IsPolyhedral [Module.Finite R N] [Module.Finite R M] (hp1 : Function.Injective p)
    (hp2 : Function.Injective p.flip) {c : PointedCone R N} (hc : IsPolyhedral p c) : c.FG := by
  rw [IsPolyhedral_def] at hc
  obtain ⟨S, S_fin, rfl⟩ := hc
  obtain ⟨T, T_fin, hT : span R S = _⟩ := IsPolyhedral_def.mp <|
    IsPolyhedral_of_fg (LinearMap.flip_flip p ▸ hp1) (fg_span S_fin)
  rw [←dual_span, hT, dual_dual_eq_span hp2 T_fin]
  exact Submodule.fg_span T_fin

theorem IsPolyhedral_iff_fg [Module.Finite R N] [Module.Finite R M] (hp1 : Function.Injective p)
    (hp2 : Function.Injective p.flip) {c : PointedCone R N} : IsPolyhedral p c ↔ c.FG :=
  ⟨fun h => fg_of_IsPolyhedral hp1 hp2 h, fun h => IsPolyhedral_of_fg hp2 h⟩
    

end LinearOrder

end PointedCone
