import Mathlib
import Toric.GroupScheme.Character
import Toric.Mathlib.RingTheory.TensorProduct.Basic

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

def U1Ring.counitAlgHom : U1Ring R →ₐ[R] R := (U1Ring.liftₐ 1 0 (by simp))

instance : CoalgebraStruct R (U1Ring R) where
  comul := U1Ring.comulAlgHom.toLinearMap
  counit := U1Ring.counitAlgHom.toLinearMap

instance : Coalgebra R (U1Ring R) where
  coassoc := by
    change (Algebra.TensorProduct.assoc _ _ _ _ _).toLinearMap ∘ₗ _ = _
    change _ ∘ₗ _ ∘ₗ U1Ring.comulAlgHom.toLinearMap = _ ∘ₗ U1Ring.comulAlgHom.toLinearMap
    change _ ∘ₗ (Algebra.TensorProduct.rTensor _).toLinearMap ∘ₗ _ = _
    change _ = (Algebra.TensorProduct.lTensor _).toLinearMap ∘ₗ _
    simp only [← AlgHom.comp_toLinearMap]
    erw [← AlgHom.comp_toLinearMap]
    -- apply AlgHom.toLinearMap_injective (R := R) (A := U1Ring R) (B := U1Ring R ⊗[R] U1Ring R ⊗[R] U1Ring R)
    sorry
  rTensor_counit_comp_comul := sorry
  lTensor_counit_comp_comul := sorry

instance : Bialgebra R (U1Ring R) where
  counit_one := by
    change U1Ring.counitAlgHom.toLinearMap _ = _
    simp
  mul_compr₂_counit := by
    ext
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply_apply, LinearMap.compl₁₂_apply]
    change U1Ring.counitAlgHom.toLinearMap _ =
      U1Ring.counitAlgHom.toLinearMap _ * U1Ring.counitAlgHom.toLinearMap _
    simp
  comul_one := by
    change U1Ring.comulAlgHom.toLinearMap _ = _
    simp
  mul_compr₂_comul := by
    ext
    simp
    change U1Ring.comulAlgHom.toLinearMap _ =
      U1Ring.comulAlgHom.toLinearMap _ * U1Ring.comulAlgHom.toLinearMap _
    simp

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
