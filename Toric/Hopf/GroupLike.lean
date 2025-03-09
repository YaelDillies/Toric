/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.RingTheory.Bialgebra.Hom
import Toric.Mathlib.LinearAlgebra.LinearIndependent.Defs
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Group-like elements in a bialgebra
-/

open TensorProduct

namespace Coalgebra
section CommSemiring
variable {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Coalgebra R A] [Coalgebra R B] {a : A}

variable (R) in
/--  A group-like element in a coalgebra is a unit `a` such that `Δ a = a ⊗ₜ a`. -/
structure IsGroupLikeElem (a : A) where
  isUnit : IsUnit a
  comul_eq_tmul_self : comul (R := R) a = a ⊗ₜ a

lemma IsGroupLikeElem.map [FunLike F A B] [BialgHomClass F R A B] (f : F)
    (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (f a) where
  isUnit := ha.isUnit.map f
  comul_eq_tmul_self := by
    rw [← CoalgHomClass.map_comp_comul_apply, ha.comul_eq_tmul_self]
    simp

lemma IsGroupLikeElem.ne_zero [Nontrivial A] (ha : IsGroupLikeElem R a) : a ≠ 0 := ha.isUnit.ne_zero

end CommSemiring

section Field
variable {F K A B : Type*} [Field K] [Ring A] [Algebra K A] [Coalgebra K A] [Nontrivial A]

open Submodule in
/-- Group-like elements over an integral domain are linearly independent. -/
lemma linearIndepOn_isGroupLikeElem : LinearIndepOn K id {a : A | IsGroupLikeElem K a} := by
  refine iSupIndep.linearIndependent (fun a ↦ span K {a.val}) (fun ⟨a, ha⟩ ↦ ?_)
    (fun a ↦ subset_span rfl) fun a ↦ a.prop.ne_zero
  simp only [← span_iUnion, Set.iUnion_subtype, ne_eq, Subtype.mk.injEq, Set.mem_setOf_eq]
  refine .symm <| disjoint_span_singleton_of_not_mem fun h ↦ ?_
  obtain ⟨s, hs, hsspan, hsindep⟩ := exists_linearIndependent K
    (⋃ b, ⋃ (_ : IsGroupLikeElem K b), ⋃ (_ : ¬b = a), {b})
  simp only [Set.subset_def, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, exists_and_left,
    exists_eq_right_right'] at hs
  rw [← hsspan, mem_span_set'] at h
  obtain ⟨n, c, e, hcea⟩ := h
  have goddamnit_mem_span_set'_didnt_give_me_this : e.Injective := sorry
  replace hs i := hs (e i) (e i).prop
  replace hsindep := hsindep.comp e goddamnit_mem_span_set'_didnt_give_me_this
  choose he hea using hs
  have := calc
        ∑ i, ∑ j, (if i = j then c i else 0) • (e i).val ⊗ₜ[K] (e j).val
    _ = ∑ i, c i • (e i).val ⊗ₜ[K] (e i).val := by simp
    _ = comul a := by simp [← hcea, (he _).comul_eq_tmul_self]
    _ = a ⊗ₜ a := ha.comul_eq_tmul_self
    _ = ∑ i, ∑ j, (c i * c j) • (e i).val ⊗ₜ[K] (e j).val := by
      simp_rw [← hcea, sum_tmul, smul_tmul, Finset.smul_sum, tmul_sum, tmul_smul, mul_smul]
  simp_rw [← Fintype.sum_prod_type'] at this
  have := (hsindep.tmul hsindep).fintypeLinearCombination_injective this
  rw [funext_iff] at this
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero <| hcea.trans_ne ha.ne_zero
  rw [smul_ne_zero_iff_left (he _).ne_zero] at hi
  refine hea i ?_
  calc
       (e i).val
    _ = (1 : K) • e i := by simp
    _ = c i • e i := by congr; simpa [hi, eq_comm] using this (i, i)
    _ = ∑ j, c j • (e j).val := by
      rw [Fintype.sum_eq_single]
      rintro j hji
      have : c j = 0 := by simpa [hji, hi] using this (j, i)
      simp [this]
    _ = a := hcea

end Field
end Coalgebra
