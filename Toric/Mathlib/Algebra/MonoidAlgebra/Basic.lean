import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MonoidAlgebra.Basic
import Toric.Mathlib.Algebra.MonoidAlgebra.Defs

namespace MonoidAlgebra

variable {k A B G : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]
    [Monoid G]

@[simp]
theorem liftNCAlgHom_single (f : A →ₐ[k] B) (g : G →* B) (h_comm) (a : G) (b : A) :
    liftNCAlgHom f g h_comm (single a b) = f b * g a :=
  liftNC_single _ _ _ _

end MonoidAlgebra

namespace MonoidAlgebra

section mapRange

variable {R S T A M N : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Monoid M] [Monoid N]

@[simp]
lemma mapDomainRingHom_comp_algebraMap (f : M →* N) :
    (mapDomainRingHom A f).comp (algebraMap R <| MonoidAlgebra A M) =
      algebraMap R (MonoidAlgebra A N) := by
  ext; simp

@[simp]
lemma mapRangeRingHom_comp_algebraMap [CommSemiring S] (f : R →+* S) :
    (mapRangeRingHom (M := M) f).comp (algebraMap _ _) = (algebraMap _ _).comp f := by
  ext
  simp

/-- The algebra homomorphism of monoid algebras induced by a homomorphism of the base algebras. -/
noncomputable def mapRangeAlgHom {T : Type*} [Semiring S]
    [Semiring T] [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) :
    MonoidAlgebra S M →ₐ[R] MonoidAlgebra T M :=
  liftNCAlgHom (singleOneAlgHom.comp f) (of T M) (by intro x y; simp[commute_iff_eq])

@[simp]
lemma mapRangeAlgHom_apply {T : Type*} [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
   (f : S →ₐ[R] T) (x : MonoidAlgebra S M) (m : M) :
    mapRangeAlgHom f x m = f (x m) := mapRangeRingHom_apply f.toRingHom x m

@[simp]
lemma mapRangeAlgHom_single {T : Type*} [Semiring S]
    [Semiring T] [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) (a : M) (b : S) :
    mapRangeAlgHom f (single a b) = single a (f b) := by
  classical
  ext
  simp [single_apply, apply_ite f]

/-- The algebra isomorphism of monoid algebras induced by an isomorphism of the base algebras. -/
@[simps apply]
noncomputable def mapRangeAlgEquiv {T : Type*} [Semiring S] [Semiring T]
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
noncomputable abbrev algebraMonoidAlgebra : Algebra (MonoidAlgebra R M) (MonoidAlgebra S M) :=
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

namespace AddMonoidAlgebra
variable {R A M N : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddMonoid M] [AddMonoid N]

@[simp]
lemma mapDomainRingHom_comp_algebraMap (f : M →+ N) :
    (mapDomainRingHom A f).comp (algebraMap R A[M]) = algebraMap R A[N] := by ext; simp

end AddMonoidAlgebra
