import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

variable {R M : Type*}

namespace MonoidAlgebra
variable [Semiring R] [MulOneClass M]

@[simp] lemma linearCombination_of : Finsupp.linearCombination R (of R M) = .id := by ext; simp

end MonoidAlgebra

namespace AddMonoidAlgebra
variable [Semiring R] [AddZeroClass M]

@[simp] lemma linearCombination_of : Finsupp.linearCombination R (of R M) = .id := by ext; simp; rfl

end AddMonoidAlgebra

