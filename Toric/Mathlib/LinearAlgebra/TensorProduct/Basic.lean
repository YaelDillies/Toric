import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N]

protected lemma LinearIndependent.tmul {ι κ : Type*} {f : ι → M} {g : κ → N}
    (hf : LinearIndependent R f) (hg : LinearIndependent R g) :
    LinearIndependent R (fun ik : ι × κ ↦ f ik.1 ⊗ₜ[R] g ik.2) := by
  rintro v w hvw
  ext ⟨i, k⟩
  sorry
