import Mathlib.Algebra.MonoidAlgebra.Basic

namespace MonoidAlgebra

variable {k A B G : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]
    [Monoid G]

@[simp]
theorem liftNCAlgHom_single (f : A →ₐ[k] B) (g : G →* B) (h_comm) (a : G) (b : A) :
    liftNCAlgHom f g h_comm (single a b) = f b * g a :=
  liftNC_single _ _ _ _

end MonoidAlgebra
