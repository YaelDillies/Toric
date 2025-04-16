/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.RingTheory.Bialgebra.Equiv
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Group-like elements in a bialgebra
-/

open Coalgebra Function TensorProduct

namespace Bialgebra
section Semiring
variable {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Bialgebra R A]
  [Bialgebra R B] {a b : A}

variable (R) in
/-- A group-like element in a coalgebra is a unit `a` such that `Δ a = a ⊗ₜ a`. -/
structure IsGroupLikeElem (a : A) where
  isUnit : IsUnit a
  comul_eq_tmul_self : comul (R := R) a = a ⊗ₜ a

lemma IsGroupLikeElem.ne_zero [Nontrivial A] (ha : IsGroupLikeElem R a) : a ≠ 0 := ha.isUnit.ne_zero

/-- The image of a group-like element by the counit is `1`, if `algebraMap R A` is injective. -/
lemma IsGroupLikeElem.counit_eq_one (hinj : Injective (algebraMap R A)) (ha : IsGroupLikeElem R a) :
    counit a = (1 : R) := hinj <| by
  simpa [ha.comul_eq_tmul_self, Ring.inverse_mul_cancel _ ha.isUnit, Algebra.smul_def] using
    congr(Algebra.TensorProduct.lid R A (((1 : R) ⊗ₜ[R] (Ring.inverse a)) *
      $(rTensor_counit_comul (R := R) a)))

/-- A bialgebra hom sends group-like elements to group-like elements. -/
lemma IsGroupLikeElem.map [FunLike F A B] [BialgHomClass F R A B] (f : F)
    (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (f a) where
  isUnit := ha.isUnit.map f
  comul_eq_tmul_self := by rw [← CoalgHomClass.map_comp_comul_apply, ha.comul_eq_tmul_self]; simp

/-- A bialgebra equivalence preserves group-like elements. -/
lemma isGroupLikeElem_map [EquivLike F A B] [BialgEquivClass F R A B] (f : F) :
    IsGroupLikeElem R (f a) ↔ IsGroupLikeElem R a where
  mp ha := by
    rw [← (BialgEquivClass.toBialgEquiv f).symm_apply_apply a]
    exact ha.map (BialgEquivClass.toBialgEquiv f).symm
  mpr := .map f

/-- In a bialgebra, `1` is a group-like element. -/
lemma IsGroupLikeElem.one : IsGroupLikeElem R (1 : A) where
  isUnit := isUnit_one
  comul_eq_tmul_self := by rw [comul_one, Algebra.TensorProduct.one_def]

/-- Group-like elements in a bialgebra are stable under multiplication. -/
lemma IsGroupLikeElem.mul (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b) :
    IsGroupLikeElem R (a * b) where
  isUnit := ha.isUnit.mul hb.isUnit
  comul_eq_tmul_self := by rw [comul_mul, ha.comul_eq_tmul_self, hb.comul_eq_tmul_self,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Group-like elements in a bialgebra are stable under inverses. -/
lemma IsGroupLikeElem.unitsInv {u : Aˣ} (ha : IsGroupLikeElem R u.val) :
    IsGroupLikeElem R u⁻¹.val where
  isUnit := u⁻¹.isUnit
  comul_eq_tmul_self := calc
          (u⁻¹.map (comulAlgHom R A)).val
      _ = (u.map (comulAlgHom R A))⁻¹.val := by simp
      _ = u⁻¹.val ⊗ₜ[R] u⁻¹.val := Units.inv_eq_of_mul_eq_one_left <| by
        simp [ha.comul_eq_tmul_self, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.one_def]

/-- Group-like elements in a bialgebra are stable under inverses. -/
lemma IsGroupLikeElem.ringInverse (ha : IsGroupLikeElem R a) :
    IsGroupLikeElem R (Ring.inverse a) := by
  simpa [← Ring.inverse_of_isUnit] using ha.unitsInv (u := ha.isUnit.unit)

variable (R A) in
/-- The group of group-like elements in a bialgebra. -/
abbrev GroupLike : Type _ := ({
  carrier := {u | IsGroupLikeElem R (u : A)}
  mul_mem' := .mul
  one_mem' := .one
  inv_mem' := .unitsInv
} : Subgroup Aˣ)

/-- Group structure on group-like elements of a bialgebra, given by multiplication. -/
instance GroupLike.instGroup : Group (GroupLike R A) := by unfold GroupLike; infer_instance

end Semiring

section CommSemiring
variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Bialgebra R A]

/-- Commutative group structure on group-like elements of a commutative bialgebra,
given by multiplication. -/
instance GroupLike.instCommGroup : CommGroup (GroupLike R A) := by unfold GroupLike; infer_instance

end CommSemiring

end Bialgebra

namespace Bialgebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A] {a b : A}

def isGroupLikeElem_one : IsGroupLikeElem R (1 : A) where
  isUnit := isUnit_one
  comul_eq_tmul_self := by rw [comul_one, Algebra.TensorProduct.one_def]

def isGroupLikeElem_mul (ha : IsGroupLikeElem R a) (hb : IsGroupLikeElem R b) :
    IsGroupLikeElem R (a * b) where
      isUnit := IsUnit.mul ha.isUnit hb.isUnit
      comul_eq_tmul_self := by rw [comul_mul, ha.comul_eq_tmul_self, hb.comul_eq_tmul_self,
        Algebra.TensorProduct.tmul_mul_tmul]

def isGroupLikeElem_inv (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (ha.isUnit.unit⁻¹).val where
  isUnit := by simp only [Units.isUnit]
  comul_eq_tmul_self := by
    have : comul (R := R) ha.isUnit.unit⁻¹.1 =
        (comulAlgHom R A).toMonoidHom ha.isUnit.unit⁻¹.1 := by dsimp
    rw [this, ← Units.coe_map_inv]
    refine (Units.eq_inv_of_mul_eq_one_left ?_).symm
    dsimp
    rw [ha.comul_eq_tmul_self, Algebra.TensorProduct.tmul_mul_tmul]
    simp only [IsUnit.mul_val_inv, Algebra.TensorProduct.one_def]

instance : Mul {a : A // IsGroupLikeElem R a} where
  mul a b := ⟨a * b, isGroupLikeElem_mul a.2 b.2⟩

instance : One {a : A // IsGroupLikeElem R a} where
  one := ⟨1, isGroupLikeElem_one⟩

instance : MulOneClass {a : A // IsGroupLikeElem R a} where
  one_mul _ := by rw [← SetCoe.ext_iff]; exact one_mul _
  mul_one _ := by rw [← SetCoe.ext_iff]; exact mul_one _

instance : Semigroup {a : A // IsGroupLikeElem R a} where
  mul_assoc _ _ _ := by rw [← SetCoe.ext_iff]; exact mul_assoc _ _ _

instance : Monoid {a : A // IsGroupLikeElem R a} where
  one_mul := one_mul
  mul_one := mul_one

noncomputable instance : Inv {a : A // IsGroupLikeElem R a} where
  inv a := ⟨a.2.isUnit.unit⁻¹.1, isGroupLikeElem_inv a.2⟩

noncomputable instance : Group {a : A // IsGroupLikeElem R a} where
  inv_mul_cancel a := by
    rw [← SetCoe.ext_iff]
    change a.2.isUnit.unit⁻¹.1 * a.2.isUnit.unit.1 = 1
    rw [Units.inv_mul]

end Bialgebra


namespace Bialgebra

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [Bialgebra R A]

instance : CommMonoid {a : A // IsGroupLikeElem R a} where
  mul_comm a b := by rw [← SetCoe.ext_iff]; exact mul_comm _ _

noncomputable instance : CommGroup {a : A // IsGroupLikeElem R a} where

end Bialgebra

namespace Bialgebra

section Field
variable {F K A B : Type*} [Field K] [Ring A] [Bialgebra K A] [Nontrivial A]

open Submodule in
/-- Group-like elements over a field are linearly independent. -/
lemma linearIndepOn_isGroupLikeElem : LinearIndepOn K id {a : A | IsGroupLikeElem K a} := by
  rw [linearIndepOn_iff_not_mem_span]
  simp only [Set.mem_setOf_eq, id_eq, Set.image_id']
  rintro a ha h
  obtain ⟨s, hs, hsspan, hsindep⟩ := exists_linearIndependent K ({b | IsGroupLikeElem K b} \ {a})
  simp only [Set.subset_def, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff] at hs
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
end Bialgebra
