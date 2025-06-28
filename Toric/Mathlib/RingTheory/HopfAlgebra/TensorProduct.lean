import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.RingTheory.TensorProduct.Basic

open scoped TensorProduct

noncomputable abbrev _root_.HopfAlgebra.ofAlgHom {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Bialgebra R A]
    (antipode : A →ₐ[R] A)
    (mul_antipode_rTensor_comul :
      ((Algebra.TensorProduct.lift antipode (.id R A) fun _ _ ↦ .all _ _).comp
        (Bialgebra.comulAlgHom R A)) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A))
    (mul_antipode_lTensor_comul :
      (Algebra.TensorProduct.lift (.id R A) antipode fun _ _ ↦ .all _ _).comp
        (Bialgebra.comulAlgHom R A) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)) :
    HopfAlgebra R A where
  antipode := antipode
  mul_antipode_rTensor_comul := by
    rw [← Algebra.TensorProduct.lmul'_comp_map] at mul_antipode_rTensor_comul
    exact congr(($mul_antipode_rTensor_comul).toLinearMap)
  mul_antipode_lTensor_comul := by
    rw [← Algebra.TensorProduct.lmul'_comp_map] at mul_antipode_lTensor_comul
    exact congr(($mul_antipode_lTensor_comul).toLinearMap)

@[simp]
lemma Bialgebra.counitAlgHom_comp_includeRight {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Bialgebra R T] :
    ((Bialgebra.counitAlgHom S (S ⊗[R] T)).restrictScalars R).comp
       Algebra.TensorProduct.includeRight =
        (Algebra.ofId R S).comp (Bialgebra.counitAlgHom R T) := by
  ext; simp [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
