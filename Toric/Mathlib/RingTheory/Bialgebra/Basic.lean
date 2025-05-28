import Mathlib.RingTheory.Bialgebra.Basic

open Coalgebra Bialgebra TensorProduct

namespace Bialgebra
variable {R C : Type*} [CommSemiring R] [Semiring C] [Bialgebra R C]

@[simp] lemma toLinearMap_counitAlgHom : (counitAlgHom R C).toLinearMap = counit := rfl

end Bialgebra
