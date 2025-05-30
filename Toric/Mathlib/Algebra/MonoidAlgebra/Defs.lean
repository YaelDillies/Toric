import Mathlib.Algebra.MonoidAlgebra.Defs

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

namespace MonoidAlgebra

open Finsupp hiding single mapDomain

universe u₁ u₂ u₃ u₄

variable {k : Type u₁} {G : Type u₂} (H : Type*) {R : Type*} [Semiring k] [Monoid G] [Semiring R]

@[simp]
theorem liftNCRingHom_single (f : k →+* R) (g : G →* R) (h_comm) (a : G) (b : k) :
    liftNCRingHom f g h_comm (single a b) = f b * g a :=
  liftNC_single _ _ _ _

end MonoidAlgebra
