/-
Copyright (c) 2025 Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mrugała
-/

import Toric.Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!

# Tensor Product of Hopf Algebras

-/

section

open TensorProduct

variable {R S T R' S' T' : Type*}
  [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra R T]
  [CommSemiring R'] [CommSemiring S'] [CommSemiring T'] [Algebra R' S'] [Algebra R' T']
  (fR : R →+* R') (fS : S →+* S') (fT : T →+* T')
  (HS : fS.comp (algebraMap _ _) = (algebraMap _ _).comp fR)
  (HT : fT.comp (algebraMap _ _) = (algebraMap _ _).comp fR)


/-- Heterobasic version of `Algebra.TensorProduct.map` as a ring homomorphism. -/
noncomputable
def Algebra.TensorProduct.mapRingHom : S ⊗[R] T →+* S' ⊗[R'] T' :=
  letI := fR.toAlgebra
  letI := ((algebraMap R' S').comp fR).toAlgebra
  letI := ((algebraMap R' T').comp fR).toAlgebra
  letI := fS.toAlgebra
  letI := fT.toAlgebra
  letI : IsScalarTower R R' S' := .of_algebraMap_eq' rfl
  letI : IsScalarTower R R' T' := .of_algebraMap_eq' rfl
  letI : IsScalarTower R S S' := .of_algebraMap_eq' HS.symm
  letI : IsScalarTower R T T' := .of_algebraMap_eq' HT.symm
  (lift (R := R) (S := R) (includeLeft.comp (IsScalarTower.toAlgHom R S S'))
    ((includeRight.restrictScalars R).comp (IsScalarTower.toAlgHom R T T'))
    (fun _ _ ↦ .all _ _)).toRingHom

@[simp]
lemma Algebra.TensorProduct.mapRingHom_tmul (s : S) (t : T) :
    mapRingHom fR fS fT HS HT (s ⊗ₜ t) = fS s ⊗ₜ fT t := by
  trans (fS s * 1 : S') ⊗ₜ[R'] (1 * fT t : T')
  · dsimp [mapRingHom, lift_tmul]; rfl
  · simp

@[simp]
lemma Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom :
    (mapRingHom fR fS fT HS HT).comp (includeLeftRingHom) = includeLeftRingHom.comp fS := by
  ext; simp

@[simp]
lemma Algebra.TensorProduct.mapRingHom_comp_includeRight :
    (mapRingHom fR fS fT HS HT).comp (RingHomClass.toRingHom includeRight) =
      (RingHomClass.toRingHom includeRight).comp fT := by
  ext; simp

end

open TensorProduct MonoidAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) [CommMonoid M]

lemma comulAlgHom_comp_mapRangeRingHom :
    (Bialgebra.comulAlgHom S (MonoidAlgebra S M)).toRingHom.comp
      (mapRangeRingHom f) =
    .comp (Algebra.TensorProduct.mapRingHom f (mapRangeRingHom f) (mapRangeRingHom f)
      (by classical ext; simp [single_apply, apply_ite f])
      (by classical ext; simp [single_apply, apply_ite f]))
      (Bialgebra.comulAlgHom R (MonoidAlgebra R M)).toRingHom := by
  ext <;> simp

lemma counitAlgHom_comp_mapRangeRingHom :
    (Bialgebra.counitAlgHom S (MonoidAlgebra S M)).toRingHom.comp
      (mapRangeRingHom f) =
    f.comp (Bialgebra.counitAlgHom R (MonoidAlgebra R M)).toRingHom := by
  ext <;> simp
