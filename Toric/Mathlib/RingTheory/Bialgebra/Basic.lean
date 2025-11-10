import Mathlib.RingTheory.Bialgebra.Basic

namespace Bialgebra
variable {R : Type*} [CommSemiring R]

@[simp] lemma counitAlgHom_self : counitAlgHom R R = .id R R := rfl

end Bialgebra
