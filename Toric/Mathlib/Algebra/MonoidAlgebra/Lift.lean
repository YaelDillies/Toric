import Mathlib.Algebra.MonoidAlgebra.Lift

namespace MonoidAlgebra
variable {R S M : Type*} [Semiring R] [Semiring S] [Monoid M]

/-- The ring homomorphism of monoid algebras induced by a homomorphism of the base rings. -/
noncomputable def mapRangeRingHom (f : R →+* S) : MonoidAlgebra R M →+* MonoidAlgebra S M :=
  liftNCRingHom (singleOneRingHom.comp f) (of S M) fun x y ↦ by simp [commute_iff_eq]

@[simp]
lemma mapRangeRingHom_apply (f : R →+* S) (x : MonoidAlgebra R M) (m : M) :
    mapRangeRingHom f x m = f (x m) := by
  induction x using MonoidAlgebra.induction_linear
  · simp
  · simp_all
  classical
  simp [mapRangeRingHom, single_apply, apply_ite (f := f)]

@[simp]
lemma mapRangeRingHom_single (f : R →+* S) (a : M) (b : R) :
    mapRangeRingHom f (single a b) = single a (f b) := by
  classical
  ext
  simp [single_apply, apply_ite f]

end MonoidAlgebra
