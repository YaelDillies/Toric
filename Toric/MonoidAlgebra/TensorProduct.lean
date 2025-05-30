/-
Copyright (c) 2025 Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mrugała
-/
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.IsTensorProduct
import Toric.Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Mathlib.Algebra.MonoidAlgebra.Basic

/-!
In this file we show that monoid algebras are stable under pushout.
-/

universe u v

noncomputable section

namespace MonoidAlgebra

open DirectSum TensorProduct

open Set LinearMap Submodule

variable {R : Type u} {N : Type v} [CommSemiring R]

variable {σ : Type*}

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Module

variable [DecidableEq σ]
variable [Semiring N] [Algebra R N]

/-- The tensor product of a monoid algebra by a module is
  linearly equivalent to a Finsupp of a tensor product. -/
noncomputable def rTensor :
    MonoidAlgebra S σ ⊗[R] N ≃ₗ[S] MonoidAlgebra (S ⊗[R] N) σ :=
  TensorProduct.finsuppLeft' _ _ _ _ _

lemma rTensor_apply_tmul (p : MonoidAlgebra S σ) (n : N) :
    rTensor (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) :=
  TensorProduct.finsuppLeft_apply_tmul p n

@[simp]
lemma rTensor_apply_tmul_apply (p : MonoidAlgebra S σ) (n : N) (d : σ) :
    rTensor (p ⊗ₜ[R] n) d = (p d) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_apply_tmul_apply p n d

lemma rTensor_apply_single_tmul (e : σ) (s : S) (n : N) (d : σ) :
    rTensor (single e s ⊗ₜ[R] n) d = if e = d then s ⊗ₜ[R] n else 0 := by
  simp only [rTensor_apply_tmul_apply, single_apply, ite_tmul]

lemma rTensor_apply (t : MonoidAlgebra S σ ⊗[R] N) (d : σ) :
    rTensor t d = ((Finsupp.lapply (R := S) d).restrictScalars R).rTensor N t :=
  TensorProduct.finsuppLeft_apply t d

@[simp]
lemma rTensor_symm_apply_single (d : σ) (s : S) (n : N) :
    rTensor.symm (.single d (s ⊗ₜ n)) =
      (single d s) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_symm_apply_single (R := R) d s n

/-- The tensor product of the monoid algebra by a module
  is linearly equivalent to a Finsupp of that module. -/
noncomputable def scalarRTensor :
    MonoidAlgebra R σ ⊗[R] N ≃ₗ[R] σ →₀ N :=
  TensorProduct.finsuppScalarLeft _ _ _

lemma scalarRTensor_apply_tmul (p : MonoidAlgebra R σ) (n : N) :
    scalarRTensor (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m • n)) :=
  TensorProduct.finsuppScalarLeft_apply_tmul p n

lemma scalarRTensor_apply_tmul_apply (p : MonoidAlgebra R σ) (n : N) (d : σ) :
    scalarRTensor (p ⊗ₜ[R] n) d = (p d) • n :=
  TensorProduct.finsuppScalarLeft_apply_tmul_apply p n d

lemma scalarRTensor_apply_single_tmul (e : σ) (r : R) (n : N) (d : σ) :
    scalarRTensor (single e r ⊗ₜ[R] n) d = if e = d then r • n else 0 := by
  rw [scalarRTensor_apply_tmul_apply, single_apply, ite_smul, zero_smul]

lemma scalarRTensor_symm_apply_single (d : σ →₀ ℕ) (n : N) :
    scalarRTensor.symm (Finsupp.single d n) = (single d 1) ⊗ₜ[R] n :=
  TensorProduct.finsuppScalarLeft_symm_apply_single d n

end Module

section Algebra

variable [CommSemiring N] [Algebra R N] [CommMonoid σ]

/-- The algebra morphism from a tensor product of a monoid algebra
  by an algebra to a monoid algebra. -/
noncomputable def rTensorAlgHom :
    (MonoidAlgebra S σ) ⊗[R] N →ₐ[S] MonoidAlgebra (S ⊗[R] N) σ :=
  Algebra.TensorProduct.lift
    (mapRangeAlgHom Algebra.TensorProduct.includeLeft)
    ((IsScalarTower.toAlgHom R (S ⊗[R] N) _).comp Algebra.TensorProduct.includeRight)
    (fun p n => by simp [commute_iff_eq, mul_comm])

@[simp]
lemma rTensorAlgHom_tmul_apply
    (p : MonoidAlgebra S σ) (n : N) (d : σ) :
    (rTensorAlgHom (p ⊗ₜ[R] n)) d = (p d) ⊗ₜ[R] n := by
  rw [rTensorAlgHom, Algebra.TensorProduct.lift_tmul]
  rw [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply]
  rw [coe_algebraMap, mul_comm, Function.comp, single_one_mul_apply]
  simp

section DecidableEq
variable [DecidableEq σ]


lemma rTensorAlgHom_single_tmul
    (e : σ) (s : S) (n : N) (d : σ) :
    (rTensorAlgHom (single e s ⊗ₜ[R] n)) d =
      if e = d then s ⊗ₜ[R] n else 0 := by
  simp [ite_tmul, single_apply]


lemma rTensorAlgHom_toLinearMap :
    (rTensorAlgHom :
      MonoidAlgebra S σ ⊗[R] N →ₐ[S] MonoidAlgebra (S ⊗[R] N) σ).toLinearMap =
      rTensor.toLinearMap := by
  ext d n e
  simp

lemma rTensorAlgHom_apply_eq (p : MonoidAlgebra S σ ⊗[R] N) :
    rTensorAlgHom (S := S) p = rTensor p := by
  rw [← AlgHom.toLinearMap_apply, rTensorAlgHom_toLinearMap]
  rfl

/-- The tensor product of a monoid algebra by an algebra
  is algebraically equivalent to a monoid algebra. -/
noncomputable def rTensorAlgEquiv :
    (MonoidAlgebra S σ) ⊗[R] N ≃ₐ[S] MonoidAlgebra (S ⊗[R] N) σ := by
  apply AlgEquiv.ofLinearEquiv rTensor
  · simp [← rTensorAlgHom_apply_eq]
  · intro x y
    simp [← rTensorAlgHom_apply_eq (S := S)]

@[simp]
lemma rTensorAlgEquiv_apply (x : (MonoidAlgebra S σ) ⊗[R] N) :
    rTensorAlgEquiv x = rTensorAlgHom x := (rTensorAlgHom_apply_eq x).symm

/-- The tensor product of the monoid algebra by an algebra `N`
  is algebraically equivalent to a monoid algebra with
  coefficients in `N`. -/
noncomputable def scalarRTensorAlgEquiv :
    MonoidAlgebra R σ ⊗[R] N ≃ₐ[R] MonoidAlgebra N σ :=
  rTensorAlgEquiv.trans (mapRangeAlgEquiv (Algebra.TensorProduct.lid R N))

end DecidableEq

variable (R)
variable {A B : Type*} [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

variable (A B) in
/-- Tensoring `MonoidAlgebra R σ` on the left by an `R`-algebra `A` is algebraically
equivalent to `MonoidAlgebra A σ`. -/
noncomputable def algebraTensorAlgEquiv :
    A ⊗[R] MonoidAlgebra B σ ≃ₐ[A] MonoidAlgebra (A ⊗[R] B) σ :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom A (A ⊗[R] B) _).comp Algebra.TensorProduct.includeLeft)
      (mapRangeAlgHom Algebra.TensorProduct.includeRight)
      (fun p n => .all _ _))
    (MonoidAlgebra.liftNCAlgHom (Algebra.TensorProduct.map (.id _ _) singleOneAlgHom)
        ((Algebra.TensorProduct.includeRight.toMonoidHom.comp (of B σ))) (fun _ _ ↦ .all _ _)) (by
      classical
      apply AlgHom.toLinearMap_injective
      ext
      simp [liftNCAlgHom, liftNCRingHom, single_one_mul_apply,
        single_apply, apply_ite ((1 : A) ⊗ₜ[R] ·)]) (by
      ext : 1
      · ext
      · apply AlgHom.toLinearMap_injective
        ext
        simp [liftNCAlgHom, liftNCRingHom, mapRangeAlgHom]
      )

@[simp]
lemma algebraTensorAlgEquiv_tmul (a : A) (p : MonoidAlgebra B σ) :
    algebraTensorAlgEquiv R A B (a ⊗ₜ p) =
      a • mapRangeAlgHom (Algebra.TensorProduct.includeRight) p := by
  simp [algebraTensorAlgEquiv, Algebra.smul_def]

@[simp]
lemma algebraTensorAlgEquiv_symm_single (m : σ) (a : A) (b : B) :
    (algebraTensorAlgEquiv R A B).symm (single m (a ⊗ₜ b)) = a ⊗ₜ single m b := by
  simp [algebraTensorAlgEquiv]

section Pushout

attribute [local instance] algebraMonoidAlgebra

instance [Algebra S B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R S A B] :
    Algebra.IsPushout R S (MonoidAlgebra A σ) (MonoidAlgebra B σ) where
  out := .of_equiv ((algebraTensorAlgEquiv (σ := σ) R S A).trans
      (mapRangeAlgEquiv (Algebra.IsPushout.equiv R S A B))).toLinearEquiv fun x ↦ by
    induction x using Finsupp.induction_linear
    · simp
    · simp_all
    · simp [mapRangeAlgHom, mapRangeRingHom, liftNCAlgHom, liftNCRingHom,
        Algebra.IsPushout.equiv_tmul]

instance [Algebra S B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R A S B] : Algebra.IsPushout R (MonoidAlgebra A σ) S (MonoidAlgebra B σ) :=
  have : Algebra.IsPushout R S A B := .symm ‹_›
  .symm inferInstance

end Pushout

end Algebra

end MonoidAlgebra

end
