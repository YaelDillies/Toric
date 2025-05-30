import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Toric.Mathlib.RingTheory.Coalgebra.Hom

suppress_compilation

open Algebra Coalgebra TensorProduct

namespace BialgHom
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B]

attribute [simp] coe_toCoalgHom

/-- TODO: Replace generic coercion. -/
abbrev toAlgHom (f : A →ₐc[R] B) : A →ₐ[R] B := f

end BialgHom

namespace Bialgebra
variable {R A : Type*} [CommSemiring R]

section Semiring
variable [Semiring A] [Bialgebra R A] {a b : A}

variable (R A) in
/-- Multiplication on a bialgebra as a coalgebra hom. -/
def mulCoalgHom : A ⊗[R] A →ₗc[R] A where
  __ := LinearMap.mul' R A
  map_smul' a b := by induction b <;> simp
  counit_comp := by ext; simp [mul_comm]
  map_comp_comul := by
    ext a b
    simp [← (ℛ R a).eq, ← (ℛ R b).eq]
    simp_rw [sum_tmul, tmul_sum]
    simp [Finset.sum_mul_sum]

@[simp] lemma mulCoalgHom_apply (a b : A) : mulCoalgHom R A (a ⊗ₜ b) = a * b := rfl

end Semiring

section CommSemiring
variable [CommSemiring A] [Bialgebra R A] {a b : A}

variable (R A) in
/-- Multiplication on a commutative bialgebra as a bialgebra hom. -/
def mulBialgHom : A ⊗[R] A →ₐc[R] A where
  __ := lmul' R
  __ := mulCoalgHom R A

@[simp] lemma mulBialgHom_apply (a b : A) : mulBialgHom R A (a ⊗ₜ b) = a * b := rfl

variable (R A) in
def comulBialgHom [IsCocomm R A] : A →ₐc[R] A ⊗[R] A where
  __ := comulAlgHom R A
  __ := comulCoalgHom R A

/-- Representations of `a` and `b` yield a representation of `a ⊗ b`. -/
@[simps]
protected def _root_.Coalgebra.Repr.tmul (ℛa : Coalgebra.Repr R a) (ℛb : Coalgebra.Repr R b) :
    Coalgebra.Repr R (a ⊗ₜ[R] b) where
  ι := ℛa.ι × ℛb.ι
  index := ℛa.index ×ˢ ℛb.index
  left i := ℛa.left i.1 ⊗ₜ ℛb.left i.2
  right i := ℛa.right i.1 ⊗ₜ ℛb.right i.2
  eq := by
    simp only [comul_def, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      AlgebraTensorModule.map_tmul]
    rw [← ℛa.eq, ← ℛb.eq]
    simp_rw [sum_tmul, tmul_sum, ← Finset.sum_product', map_sum]
    simp

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B] [Bialgebra R A]
  [Bialgebra R B] {a a₁ a₂ : A} {b : B}

/-- Representations of `a₁` and `a₂` yield a representation of `a₁ * a₂`. -/
@[simps!]
protected def _root_.Coalgebra.Repr.mul (ℛ₁ : Coalgebra.Repr R a₁) (ℛ₂ : Coalgebra.Repr R a₂) :
    Coalgebra.Repr R (a₁ * a₂) := (ℛ₁.tmul ℛ₂).induced (R := R) (mulCoalgHom R A)

attribute [simps! index] Coalgebra.Repr.mul

end CommSemiring
end Bialgebra
