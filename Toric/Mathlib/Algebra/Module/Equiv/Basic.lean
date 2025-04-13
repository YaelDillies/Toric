import Mathlib.Algebra.Module.Equiv.Basic

namespace LinearEquiv
variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

lemma one_eq_refl : (1 : M ≃ₗ[R] M) = refl R M := rfl

end LinearEquiv
