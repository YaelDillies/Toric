import Mathlib.Algebra.MonoidAlgebra.Basic

namespace MonoidAlgebra
variable {R A G H : Type*} [CommSemiring R] [Monoid G] [Monoid H] [Semiring A] [Algebra R A]

@[simp] lemma domCongr_comp_lsingle (e : G ≃* H) (g : G) :
    (domCongr R A e).toLinearMap ∘ₗ lsingle g = lsingle (e g) := by ext; simp

end MonoidAlgebra

namespace AddMonoidAlgebra
variable {R A G H : Type*} [CommSemiring R] [AddMonoid G] [AddMonoid H] [Semiring A] [Algebra R A]

@[simp] lemma domCongr_comp_lsingle (e : G ≃+ H) (g : G) :
    (domCongr R A e).toLinearMap ∘ₗ lsingle g = lsingle (e g) := by ext; simp

end AddMonoidAlgebra
