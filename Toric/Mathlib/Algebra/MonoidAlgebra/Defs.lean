import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

variable {R M : Type*}

namespace MonoidAlgebra
section Semiring
variable [Semiring R]

@[simp] lemma smul_apply (r : R) (m : M) (x : MonoidAlgebra R M) : (r • x) m = r • x m := rfl

variable [MulOneClass M]

@[simp] lemma linearCombination_of : Finsupp.linearCombination R (of R M) = .id := by ext; simp

end Semiring

section Ring
variable [Ring R]

@[simp] lemma single_neg (a : M) (b : R) : single a (-b) = -single a b := Finsupp.single_neg ..
@[simp] lemma neg_apply (m : M) (x : MonoidAlgebra R M) : (-x) m = -x m := rfl

end Ring
end MonoidAlgebra

namespace AddMonoidAlgebra
section Semiring
variable [Semiring R] [AddZeroClass M]

@[simp] lemma linearCombination_of : Finsupp.linearCombination R (of R M) = .id := by ext; simp; rfl

end Semiring

section Ring
variable [Ring R]

@[simp] lemma single_neg (a : M) (b : R) : single a (-b) = - single a b := Finsupp.single_neg ..

end Ring
end AddMonoidAlgebra

namespace MonoidAlgebra

universe u₁ u₂

variable {k : Type u₁} {G : Type u₂} [Semiring k]

section

@[simp, norm_cast] lemma coe_add (f g : MonoidAlgebra k G) : ⇑(f + g) = f + g := rfl

end

section

@[elab_as_elim]
theorem induction_linear [Monoid G] {p : MonoidAlgebra k G → Prop}
    (f : MonoidAlgebra k G) (zero : p 0) (add : ∀ f g : MonoidAlgebra k G, p f → p g → p (f + g))
    (single : ∀ a b, p (single a b)) : p f :=
  Finsupp.induction_linear f zero add single

end

end MonoidAlgebra

namespace AddMonoidAlgebra

universe u₁ u₂

variable {k : Type u₁} {G : Type u₂} [Semiring k]

section

@[simp, norm_cast] lemma coe_add (f g : AddMonoidAlgebra k G) : ⇑(f + g) = f + g := rfl

end

section

@[elab_as_elim]
theorem induction_linear [AddMonoid G] {p : AddMonoidAlgebra k G → Prop} (f : AddMonoidAlgebra k G)
    (zero : p 0) (add : ∀ f g : AddMonoidAlgebra k G, p f → p g → p (f + g))
    (single : ∀ a b, p (single a b)) : p f :=
  Finsupp.induction_linear f zero add single

end

end AddMonoidAlgebra

namespace MonoidAlgebra

open Finsupp hiding single mapDomain

universe u₁ u₂ u₃ u₄

variable {k : Type u₁} {G : Type u₂} (H : Type*) {R : Type*} [Semiring k] [Monoid G] [Semiring R]

@[simp]
theorem liftNCRingHom_single (f : k →+* R) (g : G →* R) (h_comm) (a : G) (b : k) :
    liftNCRingHom f g h_comm (single a b) = f b * g a :=
  liftNC_single _ _ _ _

end MonoidAlgebra

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
