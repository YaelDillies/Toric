import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

variable {R M : Type*}

namespace MonoidAlgebra
section Semiring
variable [Semiring R] [MulOneClass M]

@[simp] lemma linearCombination_of : Finsupp.linearCombination R (of R M) = .id := by ext; simp

end Semiring
end MonoidAlgebra

namespace AddMonoidAlgebra
variable [Semiring R] [AddZeroClass M]

@[simp] lemma linearCombination_of : Finsupp.linearCombination R (of R M) = .id := by ext; simp; rfl

end AddMonoidAlgebra

namespace AddMonoidAlgebra
variable {k G : Type*} [Semiring k]

@[elab_as_elim]
theorem induction_linear [AddMonoid G] {p : AddMonoidAlgebra k G → Prop} (f : AddMonoidAlgebra k G)
    (zero : p 0) (add : ∀ f g : AddMonoidAlgebra k G, p f → p g → p (f + g))
    (single : ∀ a b, p (single a b)) : p f :=
  Finsupp.induction_linear f zero add single

end AddMonoidAlgebra

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

end mapRange
end MonoidAlgebra
