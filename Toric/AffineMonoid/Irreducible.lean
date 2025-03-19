/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.Algebra.Module.NatInt
import Toric.Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Toric.Mathlib.Algebra.Group.Irreducible.Defs
import Toric.Mathlib.Algebra.Group.Submonoid.Basic
import Toric.Mathlib.Algebra.Group.Submonoid.BigOperators
import Toric.Mathlib.Algebra.Group.Units.Defs
import Toric.Mathlib.GroupTheory.Finiteness

/-!
# A salient affine monoid is generated by its irreducible elements

This file proves that an additive cancellative monoid with no non-zero unit is generated by its
irreducible elements.
-/

variable {M : Type*} {S : Set M}

section AddCommMonoid
variable [AddCommMonoid M] [Subsingleton (AddUnits M)]

/-- Any set `S` contains the irreducible elements of the submonoid it generates. -/
lemma addIrreducible_mem_addSubmonoidClosure_subset :
    {p ∈ AddSubmonoid.closure S | AddIrreducible p} ⊆ S := by
  refine fun x hx ↦
      AddSubmonoid.closure_induction (s := S) (p := fun x _ ↦ (AddIrreducible x → x ∈ S))
      (fun _ hx _ ↦ hx) (by simp) (fun a b _ _ ha hb h ↦ ?_) hx.1 hx.2
  obtain h₀ | h₀ := h.isAddUnit_or_isAddUnit rfl
  · obtain rfl := isAddUnit_iff_eq_zero.mp h₀
    rw [zero_add] at h ⊢
    exact hb h
  · obtain rfl := isAddUnit_iff_eq_zero.mp h₀
    rw [add_zero] at h ⊢
    exact ha h

/-- Irreducible elements lie in all sets generating a salient monoid. -/
lemma addIrreducible_subset_of_addSubmonoidClosure_eq_top (hS : AddSubmonoid.closure S = ⊤) :
    {p | AddIrreducible p} ⊆ S := by
  simpa [hS] using addIrreducible_mem_addSubmonoidClosure_subset (S := S)

lemma AddSubmonoid.FG.finite_addIrreducible_mem_addSubmonoidClosure {S : AddSubmonoid M} :
    S.FG → {p ∈ S | AddIrreducible p}.Finite := by
  rintro ⟨T, hT⟩; exact T.finite_toSet.subset <| hT ▸ addIrreducible_mem_addSubmonoidClosure_subset

variable [AddMonoid.FG M]

/-- A finitely generated salient monoid has finitely many irreducible elements. -/
lemma finite_addIrreducible : {p : M | AddIrreducible p}.Finite := by
  simpa using AddMonoid.FG.out.finite_addIrreducible_mem_addSubmonoidClosure

end AddCommMonoid

section AddCancelCommMonoid
variable [AddCancelCommMonoid M] [AddMonoid.FG M] [Subsingleton (AddUnits M)] {S : Set M}

@[simp] lemma AddSubmonoid.closure_addIrreducible :
    AddSubmonoid.closure {p : M | AddIrreducible p} = ⊤ := by
  classical
  obtain ⟨S, hSgen, hSmax⟩ := AddSubmonoid.exists_minimal_closure_eq_top M
  convert hSgen
  refine (addIrreducible_subset_of_addSubmonoidClosure_eq_top hSgen).antisymm fun r hrS ↦ ?_
  by_contra hrirred
  simp only [addIrreducible_iff, Set.mem_setOf_eq, not_and, not_forall, Classical.not_imp,
    not_or] at hrirred
  obtain rfl | hr₀ := eq_or_ne r 0
  · simpa using hSmax (y := S \ {0}) (by simpa) Finset.sdiff_subset hrS
  obtain ⟨a, b, hr, ha, hb⟩ := hrirred <| by simpa
  obtain ⟨m, hm⟩ := AddSubmonoid.mem_closure_finset (x := a).mp (by rw [hSgen]; trivial)
  obtain ⟨n, hn⟩ := AddSubmonoid.mem_closure_finset (x := b).mp (by rw [hSgen]; trivial)
  replace hm : a = m r • r + ∑ s ∈ S \ {r}, m s • s := by
    rw [hm, ← Finset.sum_sdiff <| Finset.singleton_subset_iff.2 hrS, Finset.sum_singleton, add_comm]
  replace hn : b = n r • r + ∑ s ∈ S \ {r}, n s • s := by
    rw [hn, ← Finset.sum_sdiff <| Finset.singleton_subset_iff.2 hrS, Finset.sum_singleton, add_comm]
  have hr' : r = (m r + n r) • r + ∑ s ∈ S \ {r}, m s • s + ∑ s ∈ S \ {r}, n s • s := by
    rwa [add_smul, add_assoc, add_assoc, ← add_assoc (n r • r), add_comm (n r • r) _, add_assoc,
      ← hn, ← add_assoc, ← hm]
  match hr : m r + n r with
  | 0 =>
    have : ({r} : Set M) ⊆ closure (S \ {r}) := by
      simp only [hr, zero_smul, zero_add] at hr'
      rw [hr', Set.singleton_subset_iff]
      refine add_mem ?_ ?_ <;> refine sum_mem _ fun s hs ↦ nsmul_mem (subset_closure ?_) _ <;>
        rw [← hr'] <;> simpa using hs
    specialize hSmax (y := S \ {r}) (by simp [this, hSgen]) Finset.sdiff_subset
    simpa using hSmax hrS
  | 1 =>
    simp only [hr, one_smul, add_assoc, eq_comm (a := r), add_eq_left,
      AddLeftCancelMonoid.add_eq_zero, Finset.sum_eq_zero_iff''] at hr'
    obtain h | h : m r = 0 ∨ n r = 0 := by omega
    · obtain rfl : a = 0 := by simpa [h, Finset.sum_eq_zero hr'.1] using hm
      simp at ha
    · obtain rfl : b = 0 := by simpa [h, Finset.sum_eq_zero hr'.2] using hn
      simp at hb
  | N + 2 =>
    simp [eq_comm (a := (0 : M)), hr, hr₀, add_smul, add_assoc, add_left_comm, two_nsmul] at hr'

end AddCancelCommMonoid
