import Mathlib.RingTheory.TensorProduct.Basic

open scoped TensorProduct

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

variable (R A) in
/-- Multiplication on a commutative algebra as an algebra hom. -/
protected noncomputable def AlgHom.mul : A ⊗[R] A →ₐ[R] A :=
  .ofLinearMap (.mul' R A) (by simp [Algebra.TensorProduct.one_def]) fun x y ↦ by
    induction x with
    | zero => simp
    | add => simp [add_mul, *]
    | tmul x₁ x₂ =>
    induction y with
    | zero => simp
    | add y₁ y₂ => simp [mul_add, *]
    | tmul y₁ y₂ => simp [mul_mul_mul_comm]
