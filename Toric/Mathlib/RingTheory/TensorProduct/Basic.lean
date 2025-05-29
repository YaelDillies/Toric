import Mathlib.RingTheory.TensorProduct.Basic

namespace Algebra.TensorProduct
variable {R S A B C D : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A]
  [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Semiring B] [Algebra R B] [Semiring C]
  [Algebra R C] [Algebra S C] [IsScalarTower R S C] [Semiring D] [Algebra R D]

@[simp] lemma toLinearMap_map (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    (map f g).toLinearMap = TensorProduct.AlgebraTensorModule.map f.toLinearMap g.toLinearMap := rfl

end Algebra.TensorProduct
