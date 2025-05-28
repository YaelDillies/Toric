import Mathlib.Algebra.Algebra.Defs

namespace Algebra
variable {R : Type*} [CommSemiring R]

@[simp] lemma linearMap_self : Algebra.linearMap R R = .id := rfl

end Algebra
