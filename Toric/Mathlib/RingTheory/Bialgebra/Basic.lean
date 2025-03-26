import Mathlib

open TensorProduct

section

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

noncomputable
def Bialgebra.mkAlgHoms
    (comul : A →ₐ[R] (A ⊗[R] A))
    (counit : A →ₐ[R] R)
    (h_coassoc : (Algebra.TensorProduct.assoc R A A A).toAlgHom.comp
      ((Algebra.TensorProduct.map comul (.id R A)).comp comul)
      = (Algebra.TensorProduct.map (.id R A) comul).comp comul)
    (h_rTensor : (Algebra.TensorProduct.map counit (.id R A)).comp comul
      = (Algebra.TensorProduct.lid R A).symm)
    (h_lTensor : (Algebra.TensorProduct.map (.id R A) counit).comp comul
      = (Algebra.TensorProduct.rid R R A).symm)
   :
    Bialgebra R A :=
  letI : Coalgebra R A := {
    comul := comul
    counit := counit
    coassoc := congr(($h_coassoc).toLinearMap)
    rTensor_counit_comp_comul := congr(($h_rTensor).toLinearMap)
    lTensor_counit_comp_comul := congr(($h_lTensor).toLinearMap)
  }
  .mk' _ _ (map_one counit) (map_mul counit _ _) (map_one comul) (map_mul comul _ _)

end
