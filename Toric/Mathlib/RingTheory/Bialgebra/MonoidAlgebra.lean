import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic
import Toric.Mathlib.RingTheory.Bialgebra.Equiv
import Toric.Mathlib.Algebra.MonoidAlgebra.Defs

suppress_compilation

section

open Coalgebra

variable {R A M N O : Type*}

namespace MonoidAlgebra
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Monoid M] [Monoid N] [Monoid O]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[simps!]
def domCongrBialgHom (e : M ≃* N) : MonoidAlgebra A M ≃ₐc[R] MonoidAlgebra A N :=
  .ofAlgEquiv (domCongr R A e) (by ext; simp) (by ext; simp [TensorProduct.map_map])

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : MonoidAlgebra R M ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    show (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1, MonoidAlgebra.one_def]
  right_inv := (Bialgebra.counitAlgHom R (MonoidAlgebra R M)).commutes

end MonoidAlgebra

namespace AddMonoidAlgebra
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [AddMonoid M] [AddMonoid N] [AddMonoid O]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[simps!]
def domCongrBialgHom (e : M ≃+ N) : A[M] ≃ₐc[R] A[N] :=
  .ofAlgEquiv (domCongr R A e) (by ext; simp) (by ext; simp [TensorProduct.map_map])

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    show (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1, AddMonoidAlgebra.one_def]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes

end AddMonoidAlgebra

end

namespace MonoidAlgebra

section mapRange

variable {R S M N : Type*} [Monoid M] [Monoid N]

/-- The ring homomorphism of monoid algebras induced by a homomorphism of the base rings. -/
noncomputable def mapRangeRingHom [Semiring R] [Semiring S] (f : R →+* S) :
    MonoidAlgebra R M →+* MonoidAlgebra S M :=
  liftNCRingHom (singleOneRingHom.comp f) (of S M) (by intro x y; simp [commute_iff_eq])

@[simp]
lemma mapRangeRingHom_apply [Semiring R] [Semiring S] (f : R →+* S) (x : MonoidAlgebra R M)
    (m : M) : mapRangeRingHom f x m = f (x m) := by
  induction x using MonoidAlgebra.induction_linear
  · simp
  · simp_all
  classical
  simp [mapRangeRingHom, single_apply, apply_ite (f := f)]

@[simp]
lemma mapRangeRingHom_single [Semiring R] [Semiring S] (f : R →+* S) (a : M) (b : R) :
    mapRangeRingHom f (single a b) = single a (f b) := by
  classical
  ext
  simp [single_apply, apply_ite f]

@[simp]
lemma mapRangeRingHom_comp_algebraMap [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    (mapRangeRingHom (M := M) f).comp (algebraMap _ _) = (algebraMap _ _).comp f := by
  ext
  simp

lemma mapRangeRingHom_comp_mapDomainBialgHom [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (g : M →* N) :
    (mapRangeRingHom f).comp (mapDomainBialgHom R g) =
      (RingHomClass.toRingHom (mapDomainBialgHom S g)).comp (mapRangeRingHom f) := by aesop

/-- The algebra homomorphism of monoid algebras induced by a homomorphism of the base algebras. -/
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

/-- The algebra isomorphism of monoid algebras induced by an isomorphism of the base algebras. -/
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
If `S` is an `R`-algebra, then `MonoidAlgebra S σ` is a `MonoidAlgebra R σ` algebra.

Warning: This produces a diamond for
`Algebra (MonoidAlgebra R σ) (MonoidAlgebra (MonoidAlgebra S σ) σ)`. That's why it is not a
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
