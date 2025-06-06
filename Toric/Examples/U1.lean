import Mathlib
import Toric.GroupScheme.Character

noncomputable section

notation3:max R "[X][Y]" => Polynomial (Polynomial R)
notation3:max "Y" => Polynomial.C (Polynomial.X)

open Polynomial TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (R) in
abbrev U1Ring : Type _ := R[X][Y] ⧸ Ideal.span {(X ^ 2 + Y ^ 2 - 1 : R[X][Y])}

abbrev U1Ring.mk (p : R[X][Y]) : (U1Ring R) := Ideal.Quotient.mk _ p

@[simp]
lemma U1relation : U1Ring.mk (R := R) X ^ 2 + U1Ring.mk Y ^ 2 = 1 := by
  simp_rw [← map_pow, ← RingHom.map_add]
  rw [← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.eq]
  simp
  exact Ideal.mem_span_singleton_self (X ^ 2 + Y ^ 2 - 1)

lemma U1relation' : U1Ring.mk (R := R) X ^ 2 = 1 - U1Ring.mk Y ^ 2 := by simp [← U1relation]

def Polynomial.aevalAEval {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (x y : A) :
    R[X][Y] →ₐ[R] A where
  toFun p := eval y (eval₂ (mapRingHom (algebraMap R A)) (C x) p)
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp
  commutes' r := by simp

@[simp]
lemma Polynomial.aevalAEval_X {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (x y : A) :
    Polynomial.aevalAEval (R := R) x y X = x := by simp [aevalAEval]

@[simp]
lemma Polynomial.aevalAEval_Y {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (x y : A) :
    Polynomial.aevalAEval (R := R) x y Y = y := by simp [aevalAEval]

instance : Algebra R (U1Ring R ⊗[R] U1Ring R) :=
  Algebra.TensorProduct.leftAlgebra (A := U1Ring R) (B := U1Ring R)

attribute [local simp] U1relation' in
set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
instance : CoalgebraStruct R (U1Ring R) where
  comul := (Ideal.Quotient.liftₐ _
    (aevalAEval (.mk X ⊗ₜ .mk X - .mk Y ⊗ₜ .mk Y) (.mk X ⊗ₜ .mk Y - .mk Y ⊗ₜ .mk X)) (by
    show Ideal.span _ ≤ RingHom.ker _
    simp only [Ideal.span_le, Set.singleton_subset_iff]
    simp
    ring
    erw [Algebra.TensorProduct.tmul_pow]
    sorry
    )).toLinearMap
  counit := (Ideal.Quotient.liftₐ _ (aevalAEval 1 0) (by
    show Ideal.span _ ≤ RingHom.ker _
    simp [Ideal.span_le, Set.singleton_subset_iff]
    )).toLinearMap

instance : Coalgebra R (U1Ring R) where
  coassoc := sorry
  rTensor_counit_comp_comul := sorry
  lTensor_counit_comp_comul := sorry

instance : Bialgebra R (U1Ring R) where
  counit_one := sorry
  mul_compr₂_counit := sorry
  comul_one := sorry
  mul_compr₂_comul := sorry

instance : HopfAlgebra R (U1Ring R) where
  antipode := (Ideal.Quotient.liftₐ _
    (aevalAEval (.mk X) (- .mk Y)) (by
    show Ideal.span _ ≤ RingHom.ker _
    simp only [Ideal.span_le, Set.singleton_subset_iff]
    sorry
    )).toLinearMap
  mul_antipode_rTensor_comul := sorry
  mul_antipode_lTensor_comul := sorry

def U1Ring.complexEquiv : AddMonoidAlgebra ℂ (Unit →₀ ℤ) ≃ₐc[ℂ] U1Ring ℂ where
  __ := ((MonoidAlgebra.liftGroupLikeBialgHom _ _).comp
    (MonoidAlgebra.mapDomainBialgHom ℂ (M := Multiplicative (Unit →₀ ℤ))
    (AddMonoidHom.toMultiplicative'' (.comp (zmultiplesHom _
      (.ofMul ⟨.mkOfMulEqOne (α := U1Ring ℂ)
      (.mk X + Complex.I • .mk Y) (.mk X - Complex.I • .mk Y) (by sorry), (by sorry)⟩))
      AddEquiv.finsuppUnique.toAddMonoidHom))))
  invFun := Ideal.Quotient.liftₐ _ (aevalAEval
    ((1 / 2 : ℂ) • (.single (.single .unit 1) 1 - .single (.single .unit (-1)) 1))
    (- (.I / 2 : ℂ) • (.single (.single .unit 1) 1 + .single (.single .unit (-1)) 1))) (by
    show Ideal.span _ ≤ RingHom.ker _
    simp only [Ideal.span_le, Set.singleton_subset_iff]
    sorry)
  left_inv := sorry
  right_inv := sorry

instance : Algebra S (S ⊗[R] U1Ring R) :=
  Algebra.TensorProduct.leftAlgebra (A := S) (B := U1Ring R)

def U1Ring.baseChangeEquiv : S ⊗[R] U1Ring R ≃ₐc[S] U1Ring S := by
  sorry

open AlgebraicGeometry
open scoped Hom

local notation "Spec(R)" => (Spec (CommRingCat.of R))
local notation "SO₂(R)" => (Spec (CommRingCat.of (U1Ring R)))

def foo : (Spec(R).asOver Spec(R) ⟶ SO₂(R).asOver Spec(R)) ≃*
    Matrix.specialOrthogonalGroup (Fin 2) R := sorry
