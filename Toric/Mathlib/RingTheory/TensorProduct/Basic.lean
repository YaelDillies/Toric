import Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

namespace Algebra.TensorProduct
variable {R S A B C D : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A]
  [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Semiring B] [Algebra R B] [Semiring C]
  [Algebra R C] [Algebra S C] [IsScalarTower R S C] [Semiring D] [Algebra R D]

lemma lmul'_comp_map {C : Type*} [CommSemiring C] [Algebra R C] (f : A →ₐ[R] C) (g : B →ₐ[R] C) :
    (lmul' R).comp (map f g) = lift f g (fun _ _ ↦ .all _ _) := by ext <;> rfl

lemma algebraMap_def {R S T : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra R T] :
  algebraMap S (TensorProduct R S T) = Algebra.TensorProduct.includeLeftRingHom := rfl

@[simp] lemma toLinearMap_map (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    (map f g).toLinearMap = TensorProduct.AlgebraTensorModule.map f.toLinearMap g.toLinearMap := rfl

variable (A) in
/-- `lTensor A f : A ⊗ B →ₐ A ⊗ C` is the natural algebra morphism induced by `f : B →ₐc C`. -/
noncomputable abbrev lTensor (f : B →ₐ[R] C) : (A ⊗[R] B) →ₐ[R] (A ⊗[R] C) :=
  Algebra.TensorProduct.map (.id R A) f

variable (A) in
/-- `rTensor A f : B ⊗ A →ₐc C ⊗ A` is the natural algebra morphism induced by `f : B →ₐc C`. -/
noncomputable abbrev rTensor (f : B →ₐ[R] C) : B ⊗[R] A →ₐ[R] C ⊗[R] A :=
  Algebra.TensorProduct.map f (.id R A)

end Algebra.TensorProduct

section hetero
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

end hetero

namespace Algebra.TensorProduct

variable {R A B : Type*} [CommSemiring R] [Semiring A] [CommSemiring B] [Algebra R A] [Algebra R B]

lemma algebraMap_eq_includeRight :
  letI := rightAlgebra (R := R) (A := A) (B := B)
  algebraMap B (TensorProduct R A B) = includeRight (R := R) (A := A) (B := B) := rfl

end Algebra.TensorProduct
