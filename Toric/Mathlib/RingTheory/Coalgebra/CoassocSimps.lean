/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Coalgebra.Basic
import Toric.Mathlib.RingTheory.Coalgebra.SimpAttr

/-!
# Tactic to reassociate comultiplication in a coalgebra
-/

open TensorProduct

namespace Coalgebra

variable {R A M N P M' N' P' Q Q' : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [Coalgebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q'] [Module R Q']
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N₁] [Module R N₂] [Module R N₃]

local notation3 "α" => _root_.TensorProduct.assoc R
local infix:90 " ◁ " => LinearMap.lTensor
local infix:90 " ⊗ₘ " => TensorProduct.map
local notation3:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local notation3 "δ" => comul (R := R)

attribute [coassoc_simps] LinearMap.comp_id LinearMap.id_comp TensorProduct.map_id
  LinearMap.lTensor_def LinearMap.rTensor_def LinearMap.comp_assoc
  LinearEquiv.coe_trans LinearEquiv.refl_toLinearMap TensorProduct.toLinearMap_congr
  IsCocomm.comm_comp_comul
attribute [coassoc_simps← ] TensorProduct.map_comp TensorProduct.map_map_comp_assoc_eq
  TensorProduct.map_map_comp_assoc_symm_eq
-- (λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ▷ Y

@[coassoc_simps]
lemma TensorProduct.map_comp_assoc {R₀ R R₂ R₃ : Type*} [CommSemiring R₀] [CommSemiring R]
    [CommSemiring R₂] [CommSemiring R₃] {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
    {M₀ M N M₂ M₃ N₂ N₃ : Type*} [AddCommMonoid M₀] [Module R₀ M₀]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid M₃]
    [AddCommMonoid N₃] [Module R M] [Module R N] [Module R₂ M₂] [Module R₂ N₂] [Module R₃ M₃]
    [Module R₃ N₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
    (f₂ : M₂ →ₛₗ[σ₂₃] M₃) (g₂ : N₂ →ₛₗ[σ₂₃] N₃) (f₁ : M →ₛₗ[σ₁₂] M₂) (g₁ : N →ₛₗ[σ₁₂] N₂)
    {σ₃ : R₀ →+* R₃} {σ₂ : R₀ →+* R₂} {σ₁ : R₀ →+* R}
    [RingHomCompTriple σ₂ σ₂₃ σ₃] [RingHomCompTriple σ₁ σ₁₂ σ₂] [RingHomCompTriple σ₁ σ₁₃ σ₃]
    (f : M₀ →ₛₗ[σ₁] M ⊗[R] N) :
    map f₂ g₂ ∘ₛₗ map f₁ g₁ ∘ₛₗ f = map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁) ∘ₛₗ f := by
  rw [← LinearMap.comp_assoc, TensorProduct.map_comp]

@[coassoc_simps]
lemma LinearEquiv.comp_symm_assoc {R S T M M₂ M' : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Semiring T] [AddCommMonoid M₂] [AddCommMonoid M']
    {module_M : Module R M} {module_S_M₂ : Module S M₂} {_ : Module T M'} {σ : R →+* S}
    {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ} (e : M ≃ₛₗ[σ] M₂)
    {σ'' : T →+* S} {σ''' : T →+* R} [RingHomCompTriple σ'' σ' σ''']
    [RingHomCompTriple σ''' σ σ'']
    (f : M' →ₛₗ[σ''] M₂) :
  e.toLinearMap ∘ₛₗ e.symm.toLinearMap ∘ₛₗ f = f := by ext; simp

@[coassoc_simps]
lemma LinearEquiv.symm_comp_assoc {R S T M M₂ M' : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Semiring T] [AddCommMonoid M₂] [AddCommMonoid M']
    {module_M : Module R M} {module_S_M₂ : Module S M₂} {_ : Module T M'} {σ : R →+* S}
    {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ} (e : M ≃ₛₗ[σ] M₂)
    {σ'' : T →+* S} {σ''' : T →+* R} [RingHomCompTriple σ'' σ' σ''']
    [RingHomCompTriple σ''' σ σ'']
    (f : M' →ₛₗ[σ'''] M) :
  e.symm.toLinearMap ∘ₛₗ e.toLinearMap ∘ₛₗ f = f := by ext; simp

open scoped LinearMap

@[coassoc_simps]
lemma TensorProduct.rightComm_def : rightComm R M N P =
    α _ _ _ ≪≫ₗ congr (.refl _ _) (TensorProduct.comm _ _ _) ≪≫ₗ (α _ _ _).symm := by
  sorry

@[coassoc_simps]
lemma TensorProduct.leftComm_def : leftComm R M N P =
    (α _ _ _).symm ≪≫ₗ congr (TensorProduct.comm _ _ _) (.refl _ _) ≪≫ₗ (α _ _ _) := by
  sorry

@[coassoc_simps← ]
lemma TensorProduct.map_map_comp_assoc_eq_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f : M →ₗ[R] M₁ ⊗[R] M₂ ⊗[R] M₃) :
    f₁ ⊗ₘ (f₂ ⊗ₘ f₃) ∘ₗ (α _ _ _).toLinearMap ∘ₗ f = (α N₁ N₂ N₃) ∘ₗ ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_eq]

@[coassoc_simps← ]
lemma TensorProduct.map_map_comp_assoc_symm_eq_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f : M →ₗ[R] M₁ ⊗[R] (M₂ ⊗[R] M₃)) :
    (f₁ ⊗ₘ f₂) ⊗ₘ f₃ ∘ₗ (α _ _ _).symm.toLinearMap ∘ₗ f =
      (α N₁ N₂ N₃).symm ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_symm_eq]

@[coassoc_simps]
lemma foo₁
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) :
    (α N₁ N₂ N₃).toLinearMap ∘ₗ (((f₁ ⊗ₘ f₂) ∘ₗ f₁₂) ⊗ₘ f₃) =
      (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ (α _ _ _).toLinearMap ∘ₗ (f₁₂ ⊗ₘ .id) := by
  sorry

@[coassoc_simps]
lemma foo₁_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂)
    (f : M →ₗ[R] M ⊗[R] M₃) :
    (α N₁ N₂ N₃).toLinearMap ∘ₗ (((f₁ ⊗ₘ f₂) ∘ₗ f₁₂) ⊗ₘ f₃) ∘ₗ f =
      (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ (α _ _ _).toLinearMap ∘ₗ (f₁₂ ⊗ₘ .id) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, foo₁]

@[coassoc_simps]
lemma foo₂
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    (α N₁ N₂ N₃).symm.toLinearMap ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃ ∘ₗ f₂₃)) =
      ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ (α _ _ _).symm.toLinearMap ∘ₗ (.id ⊗ₘ f₂₃) := by
  sorry
  -- simp only [← LinearMap.comp_assoc, foo₂]

@[coassoc_simps]
lemma foo₂_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃)
    (f : M →ₗ[R] M₁ ⊗[R] M) :
    (α N₁ N₂ N₃).symm.toLinearMap ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃ ∘ₗ f₂₃)) ∘ₗ f =
      ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ (α _ _ _).symm.toLinearMap ∘ₗ (.id ⊗ₘ f₂₃) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, foo₂]

@[coassoc_simps]
lemma foo₄ [Coalgebra R M] (f : M →ₗ[R] M') :
    (α _ _ _).toLinearMap ∘ₗ (comul ⊗ₘ f) ∘ₗ comul =
      (.id ⊗ₘ (.id ⊗ₘ f)) ∘ₗ (.id ⊗ₘ comul) ∘ₗ comul := by
  sorry

@[coassoc_simps]
lemma foo₄_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : N →ₗ[R] M) :
    (α _ _ _).toLinearMap ∘ₗ (comul ⊗ₘ f) ∘ₗ comul ∘ₗ g =
      (.id ⊗ₘ (.id ⊗ₘ f)) ∘ₗ (.id ⊗ₘ comul) ∘ₗ comul ∘ₗ g := by
  sorry

@[coassoc_simps]
lemma foo₅_assoc [Coalgebra R M] [IsCocomm R M] (f : N →ₗ[R] M) :
    (TensorProduct.comm R M M).toLinearMap ∘ₗ comul ∘ₗ f = comul ∘ₗ f := by
  rw [← LinearMap.comp_assoc, IsCocomm.comm_comp_comul]

lemma comp_assoc_symm (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (f₃ : P →ₗ[R] Q) :
    f₃ ∘ₗ (f₂ ∘ₗ f₁) = (f₃ ∘ₗ f₂) ∘ₗ f₁ := by simp only [coassoc_simps]

lemma map_comp_left (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g : M' →ₗ[R] N') :
    map (f₂ ∘ₗ f₁) g = map f₂ .id ∘ₗ map f₁ g := by simp only [coassoc_simps]

lemma map_comp_right (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g : M' →ₗ[R] N') :
    map g (f₂ ∘ₗ f₁) = map .id f₂ ∘ₗ map g f₁ := by simp only [coassoc_simps]

lemma map_comul_right_comp_comul (f : A →ₗ[R] M) :
    map f δ ∘ₗ δ = α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp only [coassoc_simps]

lemma map_comul_right_comp_comul_assoc (f : A →ₗ[R] M) (h : M ⊗[R] (A ⊗[R] A) →ₗ[R] P) :
    (h ∘ₗ map f δ) ∘ₗ δ = h ∘ₗ α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp only [coassoc_simps]

lemma map_comp_comul_right_comp_comul (f : A →ₗ[R] M) (g : A ⊗[R] A →ₗ[R] N) :
    map f (g ∘ₗ δ) ∘ₗ δ = M ◁ g ∘ₗ α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp only [coassoc_simps]

lemma map_comp_comul_right_comp_comul_assoc
    (f : A →ₗ[R] M) (g : A ⊗[R] A →ₗ[R] N) (h : M ⊗[R] N →ₗ[R] P) :
    (h ∘ₗ map f (g ∘ₗ δ)) ∘ₗ δ = h ∘ₗ M ◁ g ∘ₗ α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp only [coassoc_simps]

lemma map_map (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g₁ : M' →ₗ[R] N') (g₂ : N' →ₗ[R] P') :
    map f₂ g₂ ∘ₗ map f₁ g₁ = map (f₂ ∘ₗ f₁) (g₂ ∘ₗ g₁) := by
  simp only [coassoc_simps]

lemma map_map_assoc (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g₁ : M' →ₗ[R] N') (g₂ : N' →ₗ[R] P')
    (h : P ⊗[R] P' →ₗ[R] Q) :
    (h ∘ₗ map f₂ g₂) ∘ₗ map f₁ g₁ = h ∘ₗ map (f₂ ∘ₗ f₁) (g₂ ∘ₗ g₁) := by
  simp only [coassoc_simps]

lemma map_id_id : map (.id) (.id) = (.id : M ⊗[R] N →ₗ[R] _) := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_eq_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i : M' ⊗[R] (N' ⊗[R] P') →ₗ[R] Q) :
    (i ∘ₗ map f (map g h)) ∘ₗ α M N P = i ∘ₗ α M' N' P' ∘ₗ map (map f g) h := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_eq_assoc' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₁ : M' ⊗[R] Q' →ₗ[R] Q) (i₂ : N' ⊗[R] P' →ₗ[R] Q') :
    (i₁ ∘ₗ map f (i₂ ∘ₗ map g h)) ∘ₗ α M N P = i₁ ∘ₗ M' ◁ i₂ ∘ₗ α M' N' P' ∘ₗ map (map f g) h := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_eq_assoc'' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₂ : N' ⊗[R] P' →ₗ[R] Q') :
    map f (i₂ ∘ₗ map g h) ∘ₗ α M N P = M' ◁ i₂ ∘ₗ α M' N' P' ∘ₗ map (map f g) h := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_symm_eq_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i : (M' ⊗[R] N') ⊗[R] P' →ₗ[R] Q) :
    (i ∘ₗ map (map f g) h) ∘ₗ (α M N P).symm = i ∘ₗ (α M' N' P').symm ∘ₗ map f (map g h) := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_symm_eq_assoc' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₁ : Q' ⊗[R] P' →ₗ[R] Q) (i₂ : M' ⊗[R] N' →ₗ[R] Q') :
    (i₁ ∘ₗ map (i₂ ∘ₗ map f g) h) ∘ₗ (α M N P).symm =
      i₁ ∘ₗ i₂ ▷ P' ∘ₗ (α M' N' P').symm ∘ₗ map f (map g h) := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_symm_eq_assoc'' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₂ : M' ⊗[R] N' →ₗ[R] Q') :
    map (i₂ ∘ₗ map f g) h ∘ₗ (α M N P).symm = i₂ ▷ P' ∘ₗ (α M' N' P').symm ∘ₗ map f (map g h) := by
  simp only [coassoc_simps]

open Lean.Parser.Tactic in
/-- `coassoc_simps` reassociates attempts to replace `x` by
`x₁ ⊗ₜ x₂` via linearity. This is an implementation detail that is used to set up tensor products
of coalgebras, bialgebras, and hopf algebras, and shouldn't be relied on downstream. -/
scoped macro "coassoc_simps" : tactic =>
  `(tactic|
    ( simp only [coassoc_simps]
      simp only [coassoc_cleanup_simps]
      repeat congr 1; guard_goal_nums 1
      ext; rfl))

end Coalgebra
