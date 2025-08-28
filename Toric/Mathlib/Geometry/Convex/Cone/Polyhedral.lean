/-
Copyright (c) 2025 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Toric.Mathlib.Geometry.Convex.Cone.Dual

/-!
# Polyhedral cones

Given a bilinear pairing `p` between two `R`-modules `M` and `N`, we define
polyhedral cones to be pointed cones in `N` that are the dual of a finite set
in `M` (this means they are the intersection of finitely many halfspaces).

The main statement is that if both `M` and `N` are finite and the pairing is injective
in both arguments, then polyhedral cones are precisely the finitely generated cones, see
`isPolyhedral_iff_fg`. Moreover, we obtain that the dual of a polyhedral cone is again polyhedral
(`IsPolyhedral.dual`) and that the double dual of a polyhedral cone is the cone itself
(`IsPolyhedral.dual_dual_flip`, `IsPolyhedral.dual_flip_dual`).
-/

open Function Module
open Submodule hiding span

variable {R 𝕜 M N : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}
local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

namespace PointedCone
section PartialOrder
variable [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R} [p.IsPerfPair] {C C₁ C₂ : PointedCone R N}
  {s : Set M}

/-- A cone is polyhedral if it is the dual of a finite set. -/
def IsPolyhedral (C : PointedCone R N) : Prop :=
  ∃ s : Set (Module.Dual R N), s.Finite ∧ dual .id s = C

variable (p) in
lemma isPolyhedral_iff_exists_finite_dual_eq :
    IsPolyhedral C ↔ ∃ s : Set M, s.Finite ∧ dual p s = C := by
  refine (Equiv.Set.congr p.toPerfPair.symm.toEquiv).exists_congr fun s ↦ ?_
  congr!
  · exact (Set.finite_image_iff p.toPerfPair.symm.injective.injOn).symm
  · ext
    simp

alias ⟨IsPolyhedral.exists_finite_dual_eq, _⟩ := isPolyhedral_iff_exists_finite_dual_eq

lemma IsPolyhedral.dual_of_finite (hs : s.Finite) : IsPolyhedral (dual p s) :=
  (isPolyhedral_iff_exists_finite_dual_eq _).2 ⟨s, hs, rfl⟩

lemma IsPolyhedral.dual_of_fg {C : PointedCone R M} (hC : C.FG) :
    IsPolyhedral (dual p (C : Set M)) := by
  obtain ⟨s, rfl⟩ := hC; rw [dual_span]; exact .dual_of_finite s.finite_toSet

variable (p) in
lemma IsPolyhedral_iff_exists_finset : IsPolyhedral C ↔ ∃ s : Finset M, dual p s = C where
  mp hC := by obtain ⟨s, hs, rfl⟩ := hC.exists_finite_dual_eq p; exact ⟨hs.toFinset, by simp⟩
  mpr := by rintro ⟨s, rfl⟩; exact .dual_of_finite s.finite_toSet

lemma IsPolyhedral.top : IsPolyhedral (⊤ : PointedCone R N) := ⟨∅, by simp⟩

variable (p) in
@[simp] lemma IsPolyhedral.dual_dual_flip (hC : IsPolyhedral C) :
    dual p (dual p.flip (C : Set N)) = C := by
  obtain ⟨s, hs, rfl⟩ := hC.exists_finite_dual_eq p; exact dual_dual_flip_dual _

variable (p) in
@[simp] lemma IsPolyhedral.dual_flip_dual {C : PointedCone R M} (hC : IsPolyhedral C) :
    dual p.flip (dual p (C : Set M)) = C := hC.dual_dual_flip _

lemma isPolyhedral.dual_inj (hC₁ : IsPolyhedral C₁) (hC₂ : IsPolyhedral C₂) :
    dual p.flip C₁ = dual p.flip C₂ ↔ C₁ = C₂ where
  mp h := by rw [← hC₁.dual_dual_flip p, ← hC₂.dual_dual_flip p, h]
  mpr h := by rw [h]

end PartialOrder

section LinearOrder
variable [CommRing R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [Projective R M]

/-- If the module `M` is finite, then the zero cone in `M` is polyhedral. -/
lemma IsPolyhedral.bot [Module.Finite R M] : IsPolyhedral (⊥ : PointedCone R M) := by
  obtain ⟨s, hS : span R _ = ⊤⟩ := Module.Finite.fg_top (R := R≥0) (M := Module.Dual R M)
  refine ⟨s, s.finite_toSet, ?_⟩
  rw [← dual_span', hS, Submodule.top_coe, dual_univ, Submodule.zero_eq_bot]
  -- TODO: Rename to `Module.Dual.eval_injective`
  exact Module.eval_apply_injective _

end LinearOrder

section LinearOrder
variable [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup M] [Module 𝕜 M] {s : Set (Dual 𝕜 M)} {w : M}

variable (s w) in
/-- A set whose dual cone is `span 𝕜 {w} ⊔ dual p s`, see `dual_sup_span_singleton_eq_dual` -/
private noncomputable abbrev auxGenSet : Set (Dual 𝕜 M) :=
  {x ∈ s | 0 ≤ x w} ∪ .image2 (fun x y ↦ x w • y - y w • x) {x ∈ s | 0 ≤ x w} {y ∈ s | y w < 0}

private lemma auxGenSet_finite (hs : s.Finite) : (auxGenSet s w).Finite :=
  .union (hs.sep _) <| .image2 _ (hs.sep _) (hs.sep _)

variable [IsStrictOrderedRing 𝕜] {C : PointedCone 𝕜 M}

private lemma auxGenSet_subset_span : auxGenSet s w ⊆ span 𝕜 s := by
  simp only [Set.union_subset_iff, Set.image2_subset_iff, Set.mem_setOf_eq, and_imp]
  refine ⟨subset_trans (fun x hx ↦ hx.1) subset_span, fun x hxS hxw y hyS hyw ↦ ?_⟩
  simpa [sub_eq_add_neg] using add_mem (smul_mem (span 𝕜 s) ⟨x w, hxw⟩ (subset_span hyS))
    (smul_mem _ ⟨-y w, neg_nonneg.mpr hyw.le⟩ (subset_span hxS))

private lemma span_singleton_le_dual_auxGenSet : span 𝕜 {w} ≤ dual .id (auxGenSet s w) := by
  simp only [span_singleton_le_iff_mem, mem_dual, Set.mem_union, Set.mem_setOf_eq, Set.mem_image2]
  rintro z (hz | ⟨x, ⟨hxS, hxw⟩, y, ⟨hyS, hyw⟩, rfl⟩)
  · exact hz.2
  · simp [mul_comm]

/-- The crucial lemma in the proof that a finitely generated cone is polyhedral:
The sum of a polyhedral cone and the cone generated by a single ray is again polyhedral. -/
private lemma dual_auxGenSet (hs : s.Finite) :
    dual .id (auxGenSet s w) = span 𝕜 {w} ⊔ dual .id s := by
  classical
  apply ge_antisymm
  · rw [← dual_span]
    exact sup_le span_singleton_le_dual_auxGenSet <| dual_le_dual auxGenSet_subset_span
  obtain hSw | hSw := {y ∈ s | y w < 0}.eq_empty_or_nonempty
  · simp only [Set.sep_eq_empty_iff_mem_false, not_lt] at hSw
    exact le_sup_of_le_right <| dual_le_dual fun x hx => .inl ⟨hx, hSw _ hx⟩
  rw [dual_union]
  intro v ⟨hv1, hv2⟩
  rw [Submodule.mem_sup]
  replace hv2 {x y : Dual 𝕜 M} (hx : x ∈ s ∧ 0 ≤ x w) (hy : y ∈ s ∧ y w < 0) :
      y w * x v ≤ y v * x w := by
    simp only [SetLike.mem_coe, mem_dual, Set.mem_image2, Set.mem_setOf_eq,
      forall_exists_index, and_imp] at hv2
    specialize hv2 x hx.1 hx.2 y hy.1 hy.2 rfl
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      sub_nonneg] at hv2
    nth_rw 2 [mul_comm] at hv2
    exact hv2
  obtain hSv | ⟨y, hy⟩ := {y ∈ s | y w < 0 ∧ y v < 0}.eq_empty_or_nonempty
  · simp +contextual only [Set.sep_and, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff,
      Set.mem_setOf_eq, not_and, true_and, not_lt, and_imp] at hSv
    refine ⟨0, zero_mem _, v, fun x hx => ?_, zero_add _⟩
    by_cases hxw : 0 ≤ x w
    · exact hv1 ⟨hx, hxw⟩
    · exact hSv x hx (lt_of_not_ge hxw)
  lift s to Finset (Dual 𝕜 M) using hs
  let u : 𝕜 := ({y ∈ s | y w < 0}.image (fun y => y v * (y w)⁻¹)).max' <| by
    simpa [Finset.Nonempty, Set.Nonempty] using hSw.image _
  have hu : 0 ≤ u := by
    refine le_trans (mul_nonneg_of_nonpos_of_nonpos hy.2.2.le (inv_nonpos.mpr hy.2.1.le))
      (Finset.le_max' _ (y v * (y w)⁻¹) ?_)
    simp only [Finset.mem_image, Finset.mem_filter]
    exact ⟨y, ⟨hy.1, hy.2.1⟩, rfl⟩
  refine ⟨u • w, ?_, v - u • w, fun z hzS ↦ ?_, add_sub_cancel _ _⟩
  · rw [← Nonneg.mk_smul _ hu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  simp only [map_sub, map_smul, smul_eq_mul, sub_nonneg]
  obtain hzw | hzw := lt_or_ge (z w) 0
  · dsimp
    rw [← _root_.mul_le_mul_right_of_neg (inv_neg''.mpr hzw), mul_inv_cancel_right₀ hzw.ne]
    exact Finset.le_max' _ (z v * (z w)⁻¹) <|
      Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzS, hzw⟩, rfl⟩
  obtain ⟨y, hy, t_eq : _ = u⟩ := Finset.mem_image.mp <|
    ({y ∈ s | y w < 0}.image (fun y => y v * (y w)⁻¹)).max'_mem <| by
      simpa [Finset.Nonempty, Set.Nonempty] using hSw.image _
  rw [Finset.mem_filter] at hy
  rw [← t_eq, ← _root_.mul_le_mul_left_of_neg hy.2, ← mul_assoc]
  nth_rw 4 [mul_comm]
  rw [mul_inv_cancel_left₀ hy.2.ne]
  exact hv2 ⟨hzS, hzw⟩ hy

variable [AddCommGroup N] [Module 𝕜 N] {p : N →ₗ[𝕜] M →ₗ[𝕜] 𝕜} [Module.Finite 𝕜 M] {s : Set M}

variable (𝕜) in
/-- A finitely generated cone is polyhedral. -/
lemma IsPolyhedral.of_fg (hC : C.FG) : IsPolyhedral C := by
  classical
  obtain ⟨s, rfl⟩ := hC
  induction s using Finset.induction with
  | empty =>
    rw [Finset.coe_empty, span_empty]
    exact .bot
  | @insert w A hwA hA =>
    obtain ⟨s, hs, hsA⟩ := hA
    rw [Finset.coe_insert, Submodule.span_insert, ← hsA, ← dual_auxGenSet hs]
    exact ⟨_, auxGenSet_finite hs, rfl⟩

protected lemma IsPolyhedral.span (hS : s.Finite) : IsPolyhedral (span 𝕜 s) := .of_fg 𝕜 (fg_span hS)

/-- The double dual of a finite set equals the cone generated by that set. -/
lemma dual_dual_eq_span [p.IsPerfPair] {s : Set M} (hS : s.Finite) :
    dual p (dual p.flip s) = span 𝕜 s := by
  simpa using IsPolyhedral.dual_dual_flip p (.span hS)

/-- A polyhedral cone is finitely generated. -/
lemma fg_of_isPolyhedral (hC : IsPolyhedral C) : C.FG := by
  obtain ⟨s, S_fin, rfl⟩ := hC
  obtain ⟨T, T_fin, hT⟩ :=
    (IsPolyhedral.of_fg 𝕜 <| fg_span S_fin).exists_finite_dual_eq (Module.Dual.eval 𝕜 M)
  rw [← dual_span', span, ← hT, Module.Dual.eval, dual_dual_eq_span T_fin]
  exact Submodule.fg_span T_fin

alias IsPolyhedral.fg := fg_of_isPolyhedral

/-- A cone is polyhedral if and only if it is finitely generated. -/
lemma isPolyhedral_iff_fg : IsPolyhedral C ↔ C.FG := ⟨fg_of_isPolyhedral , .of_fg _⟩

/-- The dual of a polyhedral cone is again polyhedral. -/
protected lemma IsPolyhedral.dual [p.IsPerfPair] (hC : IsPolyhedral C) :
    IsPolyhedral (dual p.flip C) := .dual_of_fg (fg_of_isPolyhedral hC)

end LinearOrder
end PointedCone
