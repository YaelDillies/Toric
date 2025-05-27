import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MonoidAlgebra.Basic

-- TODO: move to Mathlib.Algebra.MonoidAlgebra.Basic

namespace MonoidAlgebra

section mapRange

variable {R S M : Type*} [Monoid M]


noncomputable def mapRangeRingHom [Semiring R] [Semiring S] (f : R →+* S) :
    MonoidAlgebra R M →+* MonoidAlgebra S M :=
  liftNCRingHom (singleOneRingHom.comp f) (of S M) (by intro x y; simp [commute_iff_eq])

@[simp]
lemma mapRangeRingHom_apply [Semiring R] [Semiring S] (f : R →+* S) (x : MonoidAlgebra R M)
    (m : M) : mapRangeRingHom f x m = f (x m) := by
  induction x using Finsupp.induction_linear
  · simp
  · simp_all [MonoidAlgebra] -- TODO: BAD
  classical
  simp [mapRangeRingHom, liftNCRingHom, single_apply, apply_ite (f := f)] --TODO: BAD

@[simp]
lemma mapRangeRingHom_single [Semiring R] [Semiring S] (f : R →+* S) (a : M) (b : R) :
    mapRangeRingHom f (single a b) = single a (f b) := by
  classical
  ext
  simp [single_apply, apply_ite f]

noncomputable def mapRangeAlgHom {T : Type*} [CommSemiring R] [Semiring S]
    [Semiring T] [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) :
    MonoidAlgebra S M →ₐ[R] MonoidAlgebra T M :=
  liftNCAlgHom (singleOneAlgHom.comp f) (of T M) (by intro x y; simp[commute_iff_eq])

@[simp]
lemma mapRangeAlgHom_apply {T : Type*} [CommSemiring R] [Semiring S]
    [Semiring T] [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) (x : MonoidAlgebra S M) (m : M) :
    mapRangeAlgHom f x m = f (x m) := mapRangeRingHom_apply f.toRingHom x m

@[simp]
lemma mapRangeAlgHom_single {T : Type*} [CommSemiring R] [Semiring S]
    [Semiring T] [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) (a : M) (b : S) :
    mapRangeAlgHom f (single a b) = single a (f b) := by
  classical
  ext
  simp [single_apply, apply_ite f]

@[simps apply]
noncomputable def mapRangeAlgEquiv {T : Type*} [CommSemiring R] [Semiring S] [Semiring T]
    [Algebra R S] [Algebra R T] (f : S ≃ₐ[R] T) :
    MonoidAlgebra S M ≃ₐ[R] MonoidAlgebra T M where
  __ := mapRangeAlgHom f
  invFun := mapRangeAlgHom (f.symm : T →ₐ[R] S)
  left_inv _ := by aesop
  right_inv _ := by aesop

end mapRange

section

variable {R S M : Type*} [CommMonoid M] [CommSemiring R] [CommSemiring S] [Algebra R S]

/--
If `S` is an `R`-algebra, then `MvPolynomial σ S` is a `MvPolynomial σ R` algebra.

Warning: This produces a diamond for
`Algebra (MvPolynomial σ R) (MvPolynomial σ (MvPolynomial σ S))`. That's why it is not a
global instance.
-/
noncomputable def algebraMonoidAlgebra :
  Algebra (MonoidAlgebra R M) (MonoidAlgebra S M) :=
  (mapRangeRingHom (algebraMap R S)).toAlgebra

attribute [local instance] algebraMonoidAlgebra

@[simp]
lemma algebraMap_def :
    algebraMap (MonoidAlgebra R M) (MonoidAlgebra S M) = mapRangeRingHom (algebraMap R S) :=
  rfl

instance {T : Type*} [CommSemiring T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] :
    IsScalarTower R (MonoidAlgebra S M) (MonoidAlgebra T M) :=
  .of_algebraMap_eq' (mapRangeAlgHom (IsScalarTower.toAlgHom R S T)).comp_algebraMap.symm

end

end MonoidAlgebra
