import Mathlib.RingTheory.Bialgebra.Equiv

open Coalgebra Function TensorProduct

namespace BialgEquiv

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]

/-- Construct a bialgebra hom from an algebra hom respecting counit and comultiplication. -/
def ofAlgEquiv' (f : A ≃ₐ[R] B) (counit_comp : counit ∘ₗ f.toLinearMap = counit)
    (map_comp_comul : map f.toLinearMap f.toLinearMap ∘ₗ comul = comul ∘ₗ f.toLinearMap) :
    A ≃ₐc[R] B := sorry

end BialgEquiv
