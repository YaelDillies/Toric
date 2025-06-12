import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.AdjoinRoot
import Toric.GroupScheme.Torus
import Toric.Mathlib.Algebra.Polynomial.AlgebraMap
import Toric.Mathlib.Data.Finsupp.Single
import Toric.Mathlib.LinearAlgebra.UnitaryGroup

noncomputable section

local notation3:max R "[X][Y]" => Polynomial (Polynomial R)
local notation3:max "Y" => Polynomial.C (Polynomial.X)

open Coalgebra Polynomial TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]


variable (R) in
def SO2Ring : Type _ := AdjoinRoot (X ^ 2 + Y ^ 2 - 1 : R[X][Y])

namespace SO2Ring

instance : CommRing (SO2Ring R) := by delta SO2Ring; infer_instance
instance : Algebra R (SO2Ring R) := by delta SO2Ring; infer_instance

def mk : R[X][Y] →ₐ[R] SO2Ring R := Ideal.Quotient.mkₐ R _

nonrec def X : SO2Ring R := .mk X
nonrec def «Y» : SO2Ring R := .mk Y

@[simp] lemma X_def : mk .X = .X (R := R) := rfl
@[simp] lemma Y_def : mk Y = .Y (R := R) := rfl

--TODO : make equiv
def liftₐ (x y : S) (H : x ^ 2 + y ^ 2 = 1) : SO2Ring R →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aevalAEval x y)
    (show Ideal.span _ ≤ RingHom.ker _ by simp [Ideal.span_le, Set.singleton_subset_iff, H])

@[simp]
lemma liftₐ_X (x y : S) (H : x ^ 2 + y ^ 2 = 1) : liftₐ (R := R) x y H .X = x := aevalAEval_X ..

@[simp]
lemma liftₐ_Y (x y : S) (H : x ^ 2 + y ^ 2 = 1) : liftₐ (R := R) x y H .Y = y := aevalAEval_Y ..

@[simp]
lemma relation : SO2Ring.X (R := R) ^ 2 + .Y ^ 2 = 1 := by
  simp_rw [SO2Ring.X, SO2Ring.Y, ← map_pow, ← map_add, ← map_one SO2Ring.mk]
  exact Ideal.Quotient.eq.mpr <| by simp [Ideal.mem_span_singleton]

lemma relation' : SO2Ring.X (R := R) ^ 2 = 1 - .Y ^ 2 := by simp [← relation]

@[simp] lemma relation'' : SO2Ring.X (R := R) * .X + .Y * .Y = 1 := by simp [← pow_two]

@[ext]
lemma algebraMap_ext {A : Type*} [Semiring A] [Algebra R A] {f g : SO2Ring R →ₐ[R] A}
    (h1 : f .X = g .X) (h2 : f .Y = g .Y) : f = g := by
  simp_rw [SO2Ring] at f g; apply Ideal.Quotient.algHom_ext; ext <;> assumption

def comulAlgHom : SO2Ring R →ₐ[R] SO2Ring R ⊗[R] SO2Ring R := by
  refine liftₐ (.X ⊗ₜ .X - .Y ⊗ₜ .Y) (.X ⊗ₜ .Y + .Y ⊗ₜ .X) ?_
  ring_nf
  simp only [Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_pow (A := SO2Ring R) (B := SO2Ring R), relation', tmul_sub,
    sub_tmul, ← Algebra.TensorProduct.one_def (A := SO2Ring R) (B := SO2Ring R)]
  ring_nf

@[simp]
lemma comulAlgHom_apply_X : comulAlgHom (R := R) .X = (.X ⊗ₜ .X - .Y ⊗ₜ .Y) := by
  simp [comulAlgHom]

@[simp]
lemma comulAlgHom_apply_Y : comulAlgHom (R := R) .Y = (.X ⊗ₜ .Y + .Y ⊗ₜ .X) := by
  simp [comulAlgHom]

def counitAlgHom : SO2Ring R →ₐ[R] R := liftₐ 1 0 (by simp)

@[simp] lemma counitAlgHom.apply_X : counitAlgHom (R := R) .X = 1 := by simp [counitAlgHom]
@[simp] lemma counitAlgHom.apply_Y : counitAlgHom (R := R) .Y = 0 := by simp [counitAlgHom]

instance : Bialgebra R (SO2Ring R) := Bialgebra.ofAlgHom comulAlgHom counitAlgHom
  (by ext <;> simp [sub_tmul, tmul_sub, tmul_add, add_tmul] <;> ring)
  (by ext <;> simp [sub_tmul, tmul_sub, tmul_add, add_tmul])
  (by ext <;> simp [sub_tmul, tmul_sub, tmul_add, add_tmul])

@[simp] lemma comul_def : comul (R := R) (A := SO2Ring R) = comulAlgHom (R := R) := rfl
@[simp] lemma counit_def : counit (R := R) (A := SO2Ring R) = counitAlgHom (R := R) := rfl

def antipodeAlgHom : SO2Ring R →ₐ[R] SO2Ring R := liftₐ .X (-.Y) (by simp)

@[simp] lemma antipodeAlgHom_X : antipodeAlgHom (R := R) .X = X := by simp [antipodeAlgHom]
@[simp] lemma antipodeAlgHom_Y : antipodeAlgHom (R := R) .Y = -.Y := by simp [antipodeAlgHom]

instance : HopfAlgebra R (SO2Ring R) := by
  refine .ofAlgHom antipodeAlgHom ?_ <| by ext <;> simp; ring_nf
  ext
  · simp [← sq]
  · simp
    ring_nf

private lemma foo : (SO2Ring.X (R := ℂ)) ^ 2 - (Complex.I • SO2Ring.Y) ^ 2 = 1 := calc
  _ = .X ^ 2 - (Complex.I • .Y) * (Complex.I • .Y) := by ring
  _ = .X ^ 2 - (Complex.I) ^ 2 • .Y ^ 2 := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
    ring_nf
  _ = _ := by simp

@[simps!]
def T : (SO2Ring ℂ)ˣ :=
  .mkOfMulEqOne (.X + Complex.I • .Y) (.X - Complex.I • .Y) (by ring_nf; simp [foo])

private def complexEquivFun : MonoidAlgebra ℂ (Multiplicative ℤ) →ₐc[ℂ] SO2Ring ℂ := by
  refine (MonoidAlgebra.liftGroupLikeBialgHom _ _).comp <|
    MonoidAlgebra.mapDomainBialgHom ℂ (M := Multiplicative ℤ) <| AddMonoidHom.toMultiplicative''  <|
     zmultiplesHom _ <| .ofMul ⟨T, isUnit_of_mul_eq_one _ (mk .X - Complex.I • mk Y) ?_, ?_⟩
  · simp
    ring_nf
    exact foo
  · simp [sub_tmul, tmul_sub, tmul_add, add_tmul]
    ring_nf
    simp only [← smul_tmul']
    rw [smul_smul]
    simp
    ring

lemma complexEquivFun_single (a : Multiplicative ℤ) (b : ℂ) :
    complexEquivFun (.single a b) = b • (T ^ a.toAdd).1 := by
  simp [complexEquivFun, Algebra.ofId_apply, Algebra.smul_def]

set_option allowUnsafeReducibility true in
attribute [local semireducible] MonoidAlgebra.single in
private def complexEquivInv : SO2Ring ℂ →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ)) := by
  refine .ofAlgHom'
    (liftₐ
      ((1 / 2 : ℂ) • (.single (.ofAdd 1) 1 + .single (.ofAdd (-1)) 1))
      (- (.I / 2 : ℂ) • (.single (.ofAdd 1) 1 - .single (.ofAdd (-1)) 1)) ?_) ?_ ?_
  · simp [pow_two, sub_mul, mul_sub, add_mul, mul_add, MonoidAlgebra.single_mul_single, ← ofAdd_add,
      ← two_nsmul, ← mul_smul, ← mul_inv_rev, div_mul_div_comm, neg_div, smul_sub,
      MonoidAlgebra.one_def]
    module
  · ext <;> simp [MonoidAlgebra.counit_single]; norm_num
  · ext
    · simp [MonoidAlgebra.comul_single, smul_add, tmul_add, add_tmul, smul_sub, sub_tmul,
        tmul_sub, neg_tmul, tmul_neg, ← smul_tmul', tmul_smul, smul_smul, div_mul_div_comm,
        Complex.I_mul_I]
      module
    · simp [MonoidAlgebra.comul_single, smul_add, tmul_add, add_tmul, smul_sub, sub_tmul, tmul_sub,
        neg_tmul, tmul_neg, ← smul_tmul', tmul_smul, smul_smul, div_mul_div_comm, Complex.I_mul_I]
      module

def complexEquiv : MonoidAlgebra ℂ (Multiplicative (ℤ)) ≃ₐc[ℂ] SO2Ring ℂ where
  __ := complexEquivFun
  __ := AlgEquiv.ofAlgHom (AlgHomClass.toAlgHom complexEquivFun) complexEquivInv
    (by
      ext
      · simp [complexEquivFun_single, complexEquivInv]
        module
      simp [complexEquivInv, complexEquivFun_single, ←two_smul, smul_smul, div_mul_eq_mul_div,
         -nsmul_eq_mul]
      module)
    (by
      ext
      simp [complexEquivFun_single, complexEquivInv, smul_smul, mul_div, smul_sub, neg_div,
        MonoidAlgebra.single, ← sub_eq_add_neg, ← Finsupp.single_add_apply, -Finsupp.single_add]
      norm_num)

def algHomMulEquiv : (SO2Ring R →ₐ[R] S) ≃* Matrix.specialOrthogonalGroup (Fin 2) S where
  toFun f := ⟨!![f .X, f .Y; - f .Y, f .X], by
    simp [← map_mul, ← map_add, Matrix.mem_specialOrthogonalGroup_fin_two_iff, pow_two]⟩
  invFun M := SO2Ring.liftₐ (M.1 0 0) (M.1 0 1)
    (Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp M.2).2.2
  left_inv f := by ext <;> simp
  right_inv M := by ext i j; fin_cases i, j <;>
    simp [(Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp M.2).2.1,
      (Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp M.2).1]
  map_mul' f g := by ext i j; fin_cases i, j <;> simp [sub_eq_add_neg, add_comm]

instance : Algebra S (S ⊗[R] SO2Ring R) :=
  Algebra.TensorProduct.leftAlgebra (A := S) (B := SO2Ring R)

def baseChangeEquiv : S ⊗[R] SO2Ring R ≃ₐc[S] SO2Ring S := sorry

end SO2Ring

open AlgebraicGeometry CategoryTheory Limits
open scoped Hom

namespace AlgebraicGeometry

scoped notation3 "SO₂("R")" => Spec <| .of <| SO2Ring R

instance : (pullback (SO₂(ℝ) ↘ Spec(ℝ)) (Spec(ℂ) ↘ Spec(ℝ))).IsSplitTorusOver Spec(ℂ) where
  existsIso := sorry

instance : Spec(SO2Ring ℝ).IsTorusOver ℝ where
  existsSplit := by
    use ℂ, inferInstance, inferInstance, inferInstance
    sorry

def bar :
    (Spec(R).asOver Spec(R) ⟶ SO₂(R).asOver Spec(R)) ≃* Matrix.specialOrthogonalGroup (Fin 2) R :=
  sorry

end AlgebraicGeometry
