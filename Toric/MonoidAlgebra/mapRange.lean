import Mathlib.Algebra.MonoidAlgebra.Basic

variable {R S M : Type*} [Monoid M]

noncomputable def MonoidAlgebra.mapRangeRingMap [Semiring R] [Semiring S] (f : R →+* S) :
    MonoidAlgebra R M →+* MonoidAlgebra S M :=
  liftNCRingHom (singleOneRingHom.comp f) (of S M) (by intro x y; simp [commute_iff_eq])

noncomputable def MonoidAlgebra.mapRangeAlgHom  {T : Type*} [CommSemiring R] [Semiring S]
    [Semiring T] [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) :
    MonoidAlgebra S M →ₐ[R] MonoidAlgebra T M :=
  liftNCAlgHom (singleOneAlgHom.comp f) (of T M) (by intro x y; simp[commute_iff_eq])
