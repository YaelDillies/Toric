import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Toric.GroupScheme.HopfAffine
import Toric.Hopf.MonoidAlgebra

noncomputable section

notation3:max R "[X][Y]" => Polynomial (Polynomial R)
notation3:max "Y" => Polynomial.C (Polynomial.X)

open Polynomial TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

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

variable (R) in
def U1Ring : Type _ := R[X][Y] ⧸ Ideal.span {(X ^ 2 + Y ^ 2 - 1 : R[X][Y])}

instance : CommRing (U1Ring R) := by delta U1Ring; infer_instance
instance : Algebra R (U1Ring R) := by delta U1Ring; infer_instance

def U1Ring.mk : R[X][Y] →ₐ[R] U1Ring R := Ideal.Quotient.mkₐ R _

nonrec def U1Ring.X : U1Ring R := .mk X
nonrec def U1Ring.Y : U1Ring R := .mk Y

@[simp]
lemma U1Ring.X_def : .mk Polynomial.X = U1Ring.X (R := R) := rfl

@[simp]
lemma U1Ring.Y_def : .mk Y = U1Ring.Y (R := R) := rfl

def U1Ring.liftₐ (x y : S) (H : x ^ 2 + y ^ 2 = 1) : U1Ring R →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aevalAEval x y)
    (show Ideal.span _ ≤ RingHom.ker _ by simp [Ideal.span_le, Set.singleton_subset_iff, H])

@[simp]
lemma U1Ring.liftₐ_X (x y : S) (H : x ^ 2 + y ^ 2 = 1) : liftₐ (R := R) x y H .X = x :=
  Polynomial.aevalAEval_X ..

@[simp]
lemma U1Ring.liftₐ_Y (x y : S) (H : x ^ 2 + y ^ 2 = 1) : liftₐ (R := R) x y H .Y = y :=
  Polynomial.aevalAEval_Y ..

@[simp]
lemma U1relation : U1Ring.X (R := R) ^ 2 + .Y ^ 2 = 1 := by
  simp_rw [U1Ring.X, U1Ring.Y, ← map_pow, ← map_add, ← map_one U1Ring.mk]
  refine Ideal.Quotient.eq.mpr (by simp [Ideal.mem_span_singleton])

lemma U1relation' : U1Ring.X (R := R) ^ 2 = 1 - .Y ^ 2 := by simp [← U1relation]

/- @[ext]
lemma U1Ring.linearMap_ext {M : Type*} [AddCommGroup M] [Module R M] {f g : U1Ring R →ₗ[R] M}
    (h1 : f .X = g .X) (h2 : f .Y = g .Y) : f = g := by
  simp_rw [U1Ring] at f g
  ext -/

@[ext]
lemma U1Ring.algebraMap_ext {A : Type*} [Semiring A] [Algebra R A] {f g : U1Ring R →ₐ[R] A}
    (h1 : f .X = g .X) (h2 : f .Y = g .Y) : f = g := by
  simp_rw [U1Ring] at f g
  apply Ideal.Quotient.algHom_ext
  ext
  · exact h2
  exact h1

def U1Ring.comulAlgHom : U1Ring R →ₐ[R] U1Ring R ⊗[R] U1Ring R :=
  (U1Ring.liftₐ (.X ⊗ₜ .X - .Y ⊗ₜ .Y) (.X ⊗ₜ .Y + .Y ⊗ₜ .X) (by
    ring_nf
    simp only [Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_pow (A := U1Ring R) (B := U1Ring R), U1relation', tmul_sub,
      sub_tmul, ← Algebra.TensorProduct.one_def (A := U1Ring R) (B := U1Ring R)]
    ring_nf))

@[simp]
lemma U1Ring.comulAlgHom_apply_X : U1Ring.comulAlgHom (R := R) .X = (.X ⊗ₜ .X - .Y ⊗ₜ .Y) := by
  simp [comulAlgHom]

@[simp]
lemma U1Ring.comulAlgHom_apply_Y : U1Ring.comulAlgHom (R := R) .Y = (.X ⊗ₜ .Y + .Y ⊗ₜ .X) := by
  simp [comulAlgHom]

def U1Ring.counitAlgHom : U1Ring R →ₐ[R] R := (U1Ring.liftₐ 1 0 (by simp))

@[simp]
lemma U1Ring.counitAlgHom.apply_X : U1Ring.counitAlgHom (R := R) .X = 1 := by simp [counitAlgHom]

@[simp]
lemma U1Ring.counitAlgHom.apply_Y : U1Ring.counitAlgHom (R := R) .Y = 0 := by simp [counitAlgHom]

instance : Bialgebra R (U1Ring R) := Bialgebra.ofAlgHom U1Ring.comulAlgHom U1Ring.counitAlgHom
  (by ext <;> simp [sub_tmul, tmul_sub, tmul_add, add_tmul] <;> ring)
  (by ext <;> simp [sub_tmul, tmul_sub, tmul_add, add_tmul])
  (by ext <;> simp [sub_tmul, tmul_sub, tmul_add, add_tmul])

@[simp]
lemma U1Ring.comul_def :
    CoalgebraStruct.comul (R := R) (A := U1Ring R) = U1Ring.comulAlgHom (R := R) := rfl

@[simp]
lemma U1Ring.counit_def :
    CoalgebraStruct.counit (R := R) (A := U1Ring R) = U1Ring.counitAlgHom (R := R) := rfl

def U1Ring.antipodeAlgHom : U1Ring R →ₐ[R] U1Ring R :=
  U1Ring.liftₐ .X (-.Y) (by simp)

@[simp]
lemma U1Ring.antipodeAlgHom.apply_X : U1Ring.antipodeAlgHom (R := R) .X = U1Ring.X := by
  simp [U1Ring.antipodeAlgHom]

@[simp]
lemma U1Ring.antipodeAlgHom.apply_Y : U1Ring.antipodeAlgHom (R := R) .Y =  -.Y := by
  simp [U1Ring.antipodeAlgHom]

instance : HopfAlgebra R (U1Ring R) :=
  .ofAlgHom U1Ring.antipodeAlgHom
  (by
    ext
    · simp
      ring_nf
      exact U1relation
    simp
    ring_nf)
  (by
    ext
    · simp
      ring_nf
      exact U1relation
    simp
    ring_nf)

private lemma foo : (U1Ring.X (R := ℂ))  ^ 2 - (Complex.I • U1Ring.Y) ^ 2 = 1 := calc
  _ = .X ^ 2 - (Complex.I • .Y) * (Complex.I • .Y) := by ring
  _ = .X ^ 2 - (Complex.I) ^ 2 • .Y ^ 2 := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
    ring_nf
  _ = _ := by simp

def U1Ring.complexEquiv : AddMonoidAlgebra ℂ (Unit →₀ ℤ) ≃ₐc[ℂ] U1Ring ℂ where
  __ := ((MonoidAlgebra.liftGroupLikeBialgHom _ _).comp
    (MonoidAlgebra.mapDomainBialgHom ℂ (M := Multiplicative (Unit →₀ ℤ))
    (AddMonoidHom.toMultiplicative'' (.comp (zmultiplesHom _
      (.ofMul ⟨.mkOfMulEqOne (α := U1Ring ℂ)
      (.mk Polynomial.X + Complex.I • .mk Y) (.mk Polynomial.X - Complex.I • .mk Y)
      (by ring_nf; simp [foo]), (by
        simp
        constructor
        · rw [isUnit_iff_exists]
          use mk Polynomial.X - Complex.I • mk Y
          constructor
          · simp
            ring_nf
            exact foo
          simp
          ring_nf
          exact foo
        simp [sub_tmul, tmul_sub, tmul_add, add_tmul]
        ring_nf
        simp only [← smul_tmul']
        rw [smul_smul]
        simp
        ring)⟩))
      AddEquiv.finsuppUnique.toAddMonoidHom))))
  invFun := U1Ring.liftₐ
    ((1 / 2 : ℂ) • (.single (.single .unit 1) 1 - .single (.single .unit (-1)) 1))
    (- (.I / 2 : ℂ) • (.single (.single .unit 1) 1 + .single (.single .unit (-1)) 1))
    (by
      simp
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

def bar : (Spec(R).asOver Spec(R) ⟶ SO₂(R).asOver Spec(R)) ≃*
    Matrix.specialOrthogonalGroup (Fin 2) R := sorry
