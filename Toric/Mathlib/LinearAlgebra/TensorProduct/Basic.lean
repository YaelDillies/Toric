import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic

variable {R : Type*} [CommSemiring R]
variable {R' : Type*} [Monoid R']
variable {R'' : Type*} [Semiring R'']
variable {A M N P Q S T : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [AddCommMonoid Q] [AddCommMonoid S] [AddCommMonoid T]
variable [Module R M] [Module R N] [Module R Q] [Module R S] [Module R T]
variable [DistribMulAction R' M]
variable [Module R'' M]

protected lemma LinearIndependent.tmul {ι κ : Type*} {f : ι → M} {g : κ → N}
    (hf : LinearIndependent R f) (hg : LinearIndependent R g) :
    LinearIndependent R (fun ik : ι × κ ↦ f ik.1 ⊗ₜ[R] g ik.2) := by
  rintro v w hvw
  ext ⟨i, k⟩
  sorry
