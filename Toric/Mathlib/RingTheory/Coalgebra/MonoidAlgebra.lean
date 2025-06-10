import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
import Toric.Mathlib.RingTheory.Coalgebra.Convolution

namespace MonoidAlgebra
variable {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp]
lemma convMul_linearMap_single (f g : MonoidAlgebra R M →ₗ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by simp

end MonoidAlgebra
