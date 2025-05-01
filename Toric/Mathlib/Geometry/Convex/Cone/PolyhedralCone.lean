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
  exact ⟨S, rfl⟩ 

theorem IsPolyhedral_top : IsPolyhedral p (⊤ : PointedCone R N) := ⟨∅, by simp⟩

@[simp]
theorem IsPolyhedral_dual_dual {c : PointedCone R N} (hc : IsPolyhedral p c) :
    dual' p (dual' p.flip (c : Set N)) = c := by
  obtain ⟨t,rfl⟩ := hc
  exact dual_dual_dual_eq_dual

end PartialOrder

section LinearOrder

variable {𝕜 M N : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup M]
  [AddCommGroup N] [Module 𝕜 M] [Module 𝕜 N] {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜}

theorem IsPolyhedral_bot [Module.Finite 𝕜 M] (hp : Function.Injective p.flip) :
    IsPolyhedral p (⊥ : PointedCone 𝕜 N) := by
  obtain ⟨S, hS : span 𝕜 _ = ⊤⟩ := (Nonneg.isFiniteModuleOver 𝕜 M).fg_top
  use S
  rw [← dual_span, hS, Submodule.top_coe, dual_univ hp, Submodule.zero_eq_bot]

variable (S : Finset M) (w : N)

variable (p) in
/-- A generating set for `dual p S ⊔ span R {w}`, see `dual_sup_span_singleton_eq_dual -/
private noncomputable abbrev dualSupSingletonGenSet : Finset M :=
  open Classical in
  {s ∈ S | 0 ≤ p s w} ∪
    .image₂ (fun x y => p x w • y - p y w • x) {s ∈ S | 0 < p s w} {s ∈ S | p s w < 0}

private lemma dualSupSingletonGenSet_subset_span :
    (dualSupSingletonGenSet p S w : Set M) ⊆ span 𝕜 (S : Set M) := by
  simp only [Finset.coe_union, Finset.coe_filter, Finset.coe_image₂, Set.union_subset_iff,
    Set.image2_subset_iff, Set.mem_setOf_eq, SetLike.mem_coe, and_imp]
  refine ⟨subset_trans (fun x hx => hx.1) subset_span, ?_⟩
  intro x hxS hxw y hyS hyw
  convert add_mem (smul_mem (span 𝕜 S) ⟨p x w, hxw.le⟩ (subset_span hyS))
    (smul_mem _ ⟨-p y w, neg_nonneg.mpr hyw.le⟩ (subset_span hxS)) using 1
  rw [sub_eq_add_neg, Nonneg.mk_smul, Nonneg.mk_smul, neg_smul]

private lemma span_singleton_le_dualSupSingletonGenSet :
    span 𝕜 {w} ≤ dual' p (dualSupSingletonGenSet p S w) := by
  simp only [Finset.coe_union, Finset.coe_filter, Finset.coe_image₂, span_singleton_le_iff_mem,
    mem_dual', Set.mem_union, Set.mem_setOf_eq, Set.mem_image2]
  rintro z (hz | ⟨x, ⟨hxS, hxw⟩, y, ⟨hyS, hyw⟩, rfl⟩)
  · exact hz.2
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      sub_nonneg]
    rw [mul_comm]

private lemma dual_sup_span_singleton_eq_dual :
    span 𝕜 {w} ⊔ dual' p S = dual' p (dualSupSingletonGenSet p S w) := by
  classical
  apply le_antisymm
  · rw [←dual_span]
    apply sup_le (span_singleton_le_dualSupSingletonGenSet S w)
    apply dual_le_dual
    exact dualSupSingletonGenSet_subset_span S w
  · simp only [Finset.coe_union, Finset.coe_filter, Finset.coe_image₂]
    rw [dual_union]
    intro v ⟨hv1, hv2⟩ 
    rw [Submodule.mem_sup]
    simp only [SetLike.mem_coe, mem_dual', Set.mem_setOf_eq, and_imp] at hv1
    simp only [SetLike.mem_coe, mem_dual', Set.mem_image2, Set.mem_setOf_eq, forall_exists_index,
      and_imp] at hv2
    by_cases h : {x ∈ S | 0 < p x w}.Nonempty
    · let t : 𝕜 := ({x ∈ S | 0 < p x w}.image (fun x => p x v * (p x w)⁻¹)).min' <|
        Finset.image_nonempty.mpr h
      have ht : t ≥ 0 := sorry
      refine ⟨t • w, ?_, v - t • w, ?_, add_sub_cancel _ _⟩
      · rw [←Nonneg.mk_smul t ht]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · sorry
    · -- easy
      sorry

theorem IsPolyhedral_of_fg [Module.Finite 𝕜 M] (hp : Function.Injective p.flip)
    {c : PointedCone 𝕜 N} (hc : c.FG) : IsPolyhedral p c := by
  classical
  obtain ⟨S, rfl⟩ := hc
  induction S using Finset.induction with
  | empty =>
    rw [Finset.coe_empty, span_empty]
    exact IsPolyhedral_bot hp
  | @insert w A hwA hA =>
    obtain ⟨S, hS⟩ := hA
    rw [Finset.coe_insert, Submodule.span_insert, hS, dual_sup_span_singleton_eq_dual]
    exact ⟨dualSupSingletonGenSet p S w, rfl⟩

lemma IsPolyhedral_span [Module.Finite 𝕜 M] (hp : Function.Injective p.flip) {S : Set N}
    (hS : S.Finite) : IsPolyhedral p (span 𝕜 S) :=
  IsPolyhedral_of_fg hp (fg_span hS)

lemma dual_dual_eq_span [Module.Finite 𝕜 M] (hp : Function.Injective p.flip) {S : Set N}
    (hS : S.Finite) : dual' p (dual' p.flip S) = span 𝕜 S := by
  nth_rw 2 [←dual_span]
  exact IsPolyhedral_dual_dual (IsPolyhedral_span hp hS)

theorem fg_of_IsPolyhedral [Module.Finite 𝕜 N] [Module.Finite 𝕜 M] (hp1 : Function.Injective p)
    (hp2 : Function.Injective p.flip) {c : PointedCone 𝕜 N} (hc : IsPolyhedral p c) : c.FG := by
  rw [IsPolyhedral_def] at hc
  obtain ⟨S, S_fin, rfl⟩ := hc
  obtain ⟨T, T_fin, hT : span 𝕜 S = _⟩ := IsPolyhedral_def.mp <|
    IsPolyhedral_of_fg (LinearMap.flip_flip p ▸ hp1) (fg_span S_fin)
  rw [←dual_span, hT, dual_dual_eq_span hp2 T_fin]
  exact Submodule.fg_span T_fin

theorem IsPolyhedral_iff_fg [Module.Finite 𝕜 N] [Module.Finite 𝕜 M] (hp1 : Function.Injective p)
    (hp2 : Function.Injective p.flip) {c : PointedCone 𝕜 N} :
    IsPolyhedral p c ↔ c.FG :=
  ⟨fun h => fg_of_IsPolyhedral hp1 hp2 h, fun h => IsPolyhedral_of_fg hp2 h⟩

theorem IsPolyhedral_dual_of_IsPolyhedral [Module.Finite 𝕜 N] [Module.Finite 𝕜 M]
    (hp1 : Function.Injective p) (hp2 : Function.Injective p.flip) {c : PointedCone 𝕜 N}
    (hc : IsPolyhedral p c) : IsPolyhedral p.flip (dual' p.flip c) :=
  IsPolyhedral_dual_of_FG (fg_of_IsPolyhedral hp1 hp2 hc)

theorem IsPolyhedral_dual_iff [Module.Finite 𝕜 N] [Module.Finite 𝕜 M]
    (hp1 : Function.Injective p) (hp2 : Function.Injective p.flip) {c : PointedCone 𝕜 N} :
    IsPolyhedral p.flip (dual' p.flip c) ↔ IsPolyhedral p c := by
  refine ⟨fun h => ?_, IsPolyhedral_dual_of_IsPolyhedral hp1 hp2⟩ 
  sorry

end LinearOrder

end PointedCone
