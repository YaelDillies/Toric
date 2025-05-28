import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace MonoidAlgebra
variable {R M : Type*} [Semiring R] [MulOneClass M]

@[simp] lemma linearCombination_of : Finsupp.linearCombination R (of R M) = .id := by ext; simp

end MonoidAlgebra

namespace AddMonoidAlgebra
variable {R M : Type*} [Semiring R] [AddZeroClass M]

@[simp] lemma linearCombination_of : Finsupp.linearCombination R (of R M) = .id := by ext; simp; rfl

end AddMonoidAlgebra
