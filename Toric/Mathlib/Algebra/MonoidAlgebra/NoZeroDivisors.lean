import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

namespace AddMonoidAlgebra
variable {R A : Type*} [Ring R] [Nontrivial R] [Nonempty A]

instance instIsDomain [IsDomain R] [AddMonoid A] [UniqueSums A] : IsDomain R[A] :=
  NoZeroDivisors.to_isDomain _

end AddMonoidAlgebra
