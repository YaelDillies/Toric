import Mathlib.RingTheory.Bialgebra.Equiv

open Coalgebra Function TensorProduct

namespace BialgEquiv

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]

/-- Construct a bialgebra hom from an algebra hom respecting counit and comultiplication. -/
def ofAlgEquiv' (f : A ≃ₐ[R] B)
    (counit_comp : (Bialgebra.counitAlgHom R B).comp f = Bialgebra.counitAlgHom R A)
    (map_comp_comul : (Algebra.TensorProduct.map f f).comp (Bialgebra.comulAlgHom R A) =
        (Bialgebra.comulAlgHom R B).comp f) : A ≃ₐc[R] B :=
  .ofAlgEquiv f congr($(counit_comp).toLinearMap) congr($(map_comp_comul).toLinearMap)

end BialgEquiv
