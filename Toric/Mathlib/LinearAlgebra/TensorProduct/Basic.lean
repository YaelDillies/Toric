import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

@[simp]
lemma TensorProduct.coe_congr
    {R : Type*} [CommSemiring R] {M N P Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    (TensorProduct.congr f g).toLinearMap = TensorProduct.map f g := rfl

protected lemma LinearIndependent.tmul {ι κ : Type*} {f : ι → M} {g : κ → N}
    (hf : LinearIndependent R f) (hg : LinearIndependent R g) :
    LinearIndependent R (fun ik : ι × κ ↦ f ik.1 ⊗ₜ[R] g ik.2) := by
  rintro v w hvw
  ext ⟨i, k⟩
  sorry
