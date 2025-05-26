import Mathlib.Algebra.MonoidAlgebra.Basic

variable {R S M : Type*} [Monoid M]

namespace MonoidAlgebra

noncomputable def mapRangeRingHom [Semiring R] [Semiring S] (f : R →+* S) :
    MonoidAlgebra R M →+* MonoidAlgebra S M :=
  liftNCRingHom (singleOneRingHom.comp f) (of S M) (by intro x y; simp [commute_iff_eq])

lemma mapRangeRingHom_apply [Semiring R] [Semiring S] (f : R →+* S) (x : MonoidAlgebra R M)
    (m : M) : mapRangeRingHom f x m = f (x m) := by
  induction x using Finsupp.induction_linear
  · simp
  · simp_all [MonoidAlgebra] -- TODO: BAD
  classical
  simp [mapRangeRingHom, liftNCRingHom, single_apply, apply_ite (f := f)] --TODO: BAD

noncomputable def mapRangeAlgHom  {T : Type*} [CommSemiring R] [Semiring S]
    [Semiring T] [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) :
    MonoidAlgebra S M →ₐ[R] MonoidAlgebra T M :=
  liftNCAlgHom (singleOneAlgHom.comp f) (of T M) (by intro x y; simp[commute_iff_eq])

end MonoidAlgebra
