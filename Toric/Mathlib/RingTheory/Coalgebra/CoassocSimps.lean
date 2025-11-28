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

local notation3 "α" => (_root_.TensorProduct.assoc R _ _ _).toLinearMap
local notation3 "α⁻¹" => (_root_.TensorProduct.assoc R _ _ _).symm.toLinearMap
local infix:90 " ◁ " => LinearMap.lTensor
local infix:90 " ⊗ₘ " => TensorProduct.map
local notation3:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local notation3 "δ" => comul (R := R)

attribute [coassoc_simps] LinearMap.comp_id LinearMap.id_comp TensorProduct.map_id
  LinearMap.lTensor_def LinearMap.rTensor_def LinearMap.comp_assoc
  LinearEquiv.coe_trans LinearEquiv.refl_toLinearMap TensorProduct.toLinearMap_congr
  IsCocomm.comm_comp_comul TensorProduct.AlgebraTensorModule.map_eq
  TensorProduct.AlgebraTensorModule.assoc_eq TensorProduct.AlgebraTensorModule.rightComm_eq
  TensorProduct.tensorTensorTensorComm TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
attribute [coassoc_simps← ] TensorProduct.map_comp TensorProduct.map_map_comp_assoc_eq
  TensorProduct.map_map_comp_assoc_symm_eq
-- (λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ▷ Y

@[coassoc_simps]
lemma TensorProduct.AlgebraTensorModule.congr_eq {R M N P Q : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q] (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    AlgebraTensorModule.congr f g = congr f g := rfl

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
    TensorProduct.assoc R _ _ _ ≪≫ₗ congr (.refl _ _) (TensorProduct.comm _ _ _) ≪≫ₗ
      (TensorProduct.assoc R _ _ _).symm := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

@[coassoc_simps]
lemma TensorProduct.leftComm_def : leftComm R M N P =
    (TensorProduct.assoc R _ _ _).symm ≪≫ₗ congr (TensorProduct.comm _ _ _) (.refl _ _) ≪≫ₗ
      (TensorProduct.assoc R _ _ _) := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

@[coassoc_simps]
lemma TensorProduct.comm_symm : (TensorProduct.comm R M N).symm = TensorProduct.comm R N M := rfl

@[coassoc_simps← ]
lemma TensorProduct.map_map_comp_assoc_eq_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f : M →ₗ[R] M₁ ⊗[R] M₂ ⊗[R] M₃) :
    f₁ ⊗ₘ (f₂ ⊗ₘ f₃) ∘ₗ α ∘ₗ f = α ∘ₗ ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_eq]

@[coassoc_simps← ]
lemma TensorProduct.map_map_comp_assoc_symm_eq_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f : M →ₗ[R] M₁ ⊗[R] (M₂ ⊗[R] M₃)) :
    (f₁ ⊗ₘ f₂) ⊗ₘ f₃ ∘ₗ α⁻¹ ∘ₗ f = α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_symm_eq]

@[coassoc_simps]
lemma asssoc_comp_map_map_comp
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) :
    α ∘ₗ (((f₁ ⊗ₘ f₂) ∘ₗ f₁₂) ⊗ₘ f₃) = (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ .id) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_eq]
  ext
  rfl

@[coassoc_simps]
lemma asssoc_comp_map_map_comp_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂)
    (f : M →ₗ[R] M ⊗[R] M₃) :
    α ∘ₗ (((f₁ ⊗ₘ f₂) ∘ₗ f₁₂) ⊗ₘ f₃) ∘ₗ f =
      (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ .id) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, asssoc_comp_map_map_comp]

@[coassoc_simps]
lemma asssoc_symm_comp_map_map_comp
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃ ∘ₗ f₂₃)) = ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ α⁻¹ ∘ₗ (.id ⊗ₘ f₂₃) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_symm_eq]
  ext
  rfl

@[coassoc_simps]
lemma asssoc_symm_comp_map_map_comp_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃)
    (f : N →ₗ[R] M₁ ⊗[R] M) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃ ∘ₗ f₂₃)) ∘ₗ f = ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ α⁻¹ ∘ₗ (.id ⊗ₘ f₂₃) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, asssoc_symm_comp_map_map_comp]

@[coassoc_simps]
lemma assoc_symm_comp_lid_symm :
    α⁻¹ ∘ₗ (TensorProduct.lid R (M ⊗[R] N)).symm.toLinearMap =
      (TensorProduct.lid R _).symm.toLinearMap ⊗ₘ .id := rfl

@[coassoc_simps]
lemma assoc_symm_comp_lid_symm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ (TensorProduct.lid R (M ⊗[R] N)).symm.toLinearMap ∘ₗ f =
      (TensorProduct.lid R _).symm.toLinearMap ⊗ₘ .id ∘ₗ f := rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_lid_symm (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ f ⊗ₘ (TensorProduct.lid R N).symm.toLinearMap =
      (f ⊗ₘ .id ∘ₗ (TensorProduct.rid R M).symm.toLinearMap) ⊗ₘ .id := by
  ext; rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_lid_symm_assoc (f : M →ₗ[R] M') (g : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ f ⊗ₘ (TensorProduct.lid R N).symm.toLinearMap ∘ₗ g =
      (f ⊗ₘ .id ∘ₗ (TensorProduct.rid R M).symm.toLinearMap) ⊗ₘ .id ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_lid_symm]

@[coassoc_simps]
lemma assoc_symm_comp_map_rid_symm (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ f ⊗ₘ (TensorProduct.rid R N).symm.toLinearMap =
      (f ⊗ₘ .id) ⊗ₘ .id ∘ₗ (TensorProduct.rid R (M ⊗[R] N)).symm.toLinearMap := by
  ext; rfl

@[coassoc_simps]
lemma assoc_symm_comp_map_rid_symm_assoc (f : M →ₗ[R] M') (g : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ f ⊗ₘ (TensorProduct.rid R N).symm.toLinearMap ∘ₗ g =
      (f ⊗ₘ .id) ⊗ₘ .id ∘ₗ (TensorProduct.rid R (M ⊗[R] N)).symm.toLinearMap ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_rid_symm]

@[coassoc_simps]
lemma assoc_comp_rid_symm :
    α ∘ₗ (TensorProduct.rid R (M ⊗[R] N)).symm.toLinearMap =
      .id ⊗ₘ (TensorProduct.rid R _).symm.toLinearMap := by ext; rfl

@[coassoc_simps]
lemma assoc_comp_rid_symm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ (TensorProduct.rid R (M ⊗[R] N)).symm.toLinearMap ∘ₗ f =
      .id ⊗ₘ (TensorProduct.rid R _).symm.toLinearMap ∘ₗ f := by
  simp_rw [← assoc_comp_rid_symm, LinearMap.comp_assoc]

@[coassoc_simps]
lemma assoc_comp_map_lid_symm (f : N →ₗ[R] N') :
    α ∘ₗ (TensorProduct.lid R M).symm.toLinearMap ⊗ₘ f =
      (.id ⊗ₘ (.id ⊗ₘ f)) ∘ₗ (TensorProduct.lid R (M ⊗[R] N)).symm.toLinearMap := by
  ext; rfl

@[coassoc_simps]
lemma assoc_comp_map_lid_symm_assoc (f : N →ₗ[R] N') (g : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ (TensorProduct.lid R M).symm.toLinearMap ⊗ₘ f ∘ₗ g =
      (.id ⊗ₘ (.id ⊗ₘ f)) ∘ₗ (TensorProduct.lid R (M ⊗[R] N)).symm.toLinearMap ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_lid_symm]

@[coassoc_simps]
lemma assoc_comp_map_rid_symm (f : N →ₗ[R] N') :
    α ∘ₗ (TensorProduct.rid R M).symm.toLinearMap ⊗ₘ f =
      .id ⊗ₘ ((.id ⊗ₘ f) ∘ₗ (TensorProduct.lid R _).symm.toLinearMap) := by
  ext; rfl

@[coassoc_simps]
lemma assoc_comp_map_rid_symm_assoc (f : N →ₗ[R] N') (g : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ (TensorProduct.rid R M).symm.toLinearMap ⊗ₘ f ∘ₗ g =
      .id ⊗ₘ ((.id ⊗ₘ f) ∘ₗ (TensorProduct.lid R _).symm.toLinearMap) ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_rid_symm]

@[coassoc_simps]
lemma lid_symm_comp (f : M →ₗ[R] M') :
    (TensorProduct.lid R M').symm.toLinearMap ∘ₗ f =
      (.id ⊗ₘ f) ∘ₗ (TensorProduct.lid R M).symm.toLinearMap := by
  ext; rfl

@[coassoc_simps]
lemma rid_symm_comp (f : M →ₗ[R] M') :
    (TensorProduct.rid R M').symm.toLinearMap ∘ₗ f =
      (f ⊗ₘ .id) ∘ₗ (TensorProduct.rid R M).symm.toLinearMap := by
  ext; rfl

@[coassoc_simps]
lemma symm_comp_lid_symm :
    (TensorProduct.comm R _ _).toLinearMap ∘ₗ (TensorProduct.lid R M).symm.toLinearMap =
      (TensorProduct.rid R M).symm := rfl

@[coassoc_simps]
lemma symm_comp_lid_symm_assoc (f : M →ₗ[R] M') :
    (TensorProduct.comm R _ _).toLinearMap ∘ₗ (TensorProduct.lid R _).symm.toLinearMap ∘ₗ f =
      (TensorProduct.rid R _).symm.toLinearMap ∘ₗ f := rfl

@[coassoc_simps]
lemma symm_comp_rid_symm :
    (TensorProduct.comm R _ _).toLinearMap ∘ₗ (TensorProduct.rid R M).symm.toLinearMap =
      (TensorProduct.lid R M).symm := rfl

@[coassoc_simps]
lemma symm_comp_rid_symm_assoc (f : M →ₗ[R] M') :
    (TensorProduct.comm R _ _).toLinearMap ∘ₗ (TensorProduct.rid R _).symm.toLinearMap ∘ₗ f =
      (TensorProduct.lid R _).symm.toLinearMap ∘ₗ f := rfl

@[coassoc_simps]
lemma symm_comp_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    (TensorProduct.comm R M' N').toLinearMap ∘ₗ (f ⊗ₘ g) =
      (g ⊗ₘ f) ∘ₗ (TensorProduct.comm R M N).toLinearMap := by ext; rfl

@[coassoc_simps]
lemma symm_comp_map_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (h : P →ₗ[R] M ⊗[R] N) :
    (TensorProduct.comm R M' N').toLinearMap ∘ₗ (f ⊗ₘ g) ∘ₗ h =
      (g ⊗ₘ f) ∘ₗ (TensorProduct.comm R M N).toLinearMap ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, symm_comp_map]

@[coassoc_simps]
lemma comm_comp_comm :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap = .id :=
  (TensorProduct.comm R M N).symm_comp

@[coassoc_simps]
lemma comm_comp_comm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap ∘ₗ f = f := by
  rw [← LinearMap.comp_assoc, comm_comp_comm, LinearMap.id_comp]

@[coassoc_simps]
lemma coassoc_left [Coalgebra R M] (f : M →ₗ[R] M') :
    α ∘ₗ (δ ⊗ₘ f) ∘ₗ δ = (.id ⊗ₘ (.id ⊗ₘ f)) ∘ₗ (.id ⊗ₘ δ) ∘ₗ δ := by
  simp_rw [← LinearMap.lTensor_def, ← coassoc, ← LinearMap.comp_assoc, LinearMap.lTensor_def,
    map_map_comp_assoc_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
lemma coassoc_left_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : N →ₗ[R] M) :
    α ∘ₗ (δ ⊗ₘ f) ∘ₗ δ ∘ₗ g = (.id ⊗ₘ (.id ⊗ₘ f)) ∘ₗ (.id ⊗ₘ δ) ∘ₗ δ ∘ₗ g := by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

@[coassoc_simps]
lemma coassoc_right [Coalgebra R M] (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ (f ⊗ₘ δ) ∘ₗ δ = ((f ⊗ₘ .id) ⊗ₘ .id) ∘ₗ (δ ⊗ₘ .id) ∘ₗ δ := by
  simp_rw [← LinearMap.rTensor_def, ← coassoc_symm, ← LinearMap.comp_assoc, LinearMap.rTensor_def,
    map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
lemma coassoc_right_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : N →ₗ[R] M) :
    α⁻¹ ∘ₗ (f ⊗ₘ δ) ∘ₗ δ ∘ₗ g = ((f ⊗ₘ .id) ⊗ₘ .id) ∘ₗ (δ ⊗ₘ .id) ∘ₗ δ ∘ₗ g := by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

lemma map_counit_comp_comul_left [Coalgebra R M] (f : M →ₗ[R] M') :
    (counit ⊗ₘ f) ∘ₗ δ = (.id ⊗ₘ f) ∘ₗ (TensorProduct.lid _ _).symm.toLinearMap := by
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc, Coalgebra.rTensor_counit_comp_comul]
  rfl

lemma map_counit_comp_comul_left_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : P →ₗ[R] M) :
    (counit ⊗ₘ f) ∘ₗ δ ∘ₗ g = (.id ⊗ₘ f) ∘ₗ (TensorProduct.lid _ _).symm.toLinearMap ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_left]

lemma map_counit_comp_comul_right [Coalgebra R M] (f : M →ₗ[R] M') :
    (f ⊗ₘ counit) ∘ₗ δ = (f ⊗ₘ .id) ∘ₗ (TensorProduct.rid _ _).symm.toLinearMap := by
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_assoc, Coalgebra.lTensor_counit_comp_comul]
  rfl

lemma map_counit_comp_comul_right_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : P →ₗ[R] M) :
    (f ⊗ₘ counit) ∘ₗ δ ∘ₗ g = (f ⊗ₘ .id) ∘ₗ (TensorProduct.rid _ _).symm.toLinearMap ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_right]

-- lemma TensorProduct.comm_tensorProduct_right :
--     TensorProduct.comm R M (N ⊗[R] P) =
--     (TensorProduct.assoc _ _ _ _).symm ≪≫ₗ
--     TensorProduct.congr (TensorProduct.comm _ _ _) (.refl _ _) ≪≫ₗ
--     (TensorProduct.assoc _ _ _ _) ≪≫ₗ
--     TensorProduct.congr (.refl _ _) (TensorProduct.comm _ _ _) ≪≫ₗ
--     (TensorProduct.assoc _ _ _ _).symm := by
--   apply LinearEquiv.toLinearMap_injective
--   ext
--   rfl

-- @[coassoc_simps]
-- lemma foo₇ (f : M' →ₗ[R] M) (g : N' →ₗ[R] N ⊗[R] P)
--     (f' : P →ₗ[R] Q) (f'' : N →ₗ[R] Q') :
--     f'' ⊗ₘ (TensorProduct.comm R M Q).toLinearMap ∘ₗ
--         α ∘ₗ (TensorProduct.comm R M N).toLinearMap ⊗ₘ f' ∘ₗ
--         α⁻¹ ∘ₗ f ⊗ₘ g =
--     f'' ⊗ₘ (f' ⊗ₘ .id) ∘ₗ α ∘ₗ g ⊗ₘ f ∘ₗ ↑(TensorProduct.comm R M' N') := by
--   simp_rw [← foo₆ f g, ← LinearMap.comp_assoc]
--   congr 1
--   ext
--   rfl

-- @[coassoc_simps]
-- lemma foo₇_assoc (f : M' →ₗ[R] M) (g : N' →ₗ[R] N ⊗[R] P) (h : P' →ₗ[R] M' ⊗[R] N')
--     (f' : P →ₗ[R] Q) (f'' : N →ₗ[R] Q') :
--     f'' ⊗ₘ (TensorProduct.comm R M Q).toLinearMap ∘ₗ
--         α ∘ₗ (TensorProduct.comm R M N).toLinearMap ⊗ₘ f' ∘ₗ
--         α⁻¹ ∘ₗ f ⊗ₘ g ∘ₗ h = f'' ⊗ₘ (f' ⊗ₘ .id) ∘ₗ α ∘ₗ
--         g ⊗ₘ f ∘ₗ ↑(TensorProduct.comm R M' N') ∘ₗ h := by
--   simp_rw [← LinearMap.comp_assoc]
--   congr 1
--   simp_rw [LinearMap.comp_assoc, foo₇]


-- @[coassoc_simps]
-- lemma foo₈ (f : M' →ₗ[R] M) (g : N' →ₗ[R] N ⊗[R] P) (f' : P →ₗ[R] Q) (f'' : N →ₗ[R] Q') :
--     (TensorProduct.comm R _ _).toLinearMap ⊗ₘ f' ∘ₗ
--         α⁻¹ ∘ₗ f'' ⊗ₘ (TensorProduct.comm R _ _).toLinearMap ∘ₗ
--         α ∘ₗ g ⊗ₘ f =
--     ((.id ⊗ₘ f'') ⊗ₘ f') ∘ₗ α⁻¹ ∘ₗ (f ⊗ₘ g) ∘ₗ
--       (TensorProduct.comm R _ _).toLinearMap := by
--   simp_rw [← foo₆ g f, ← LinearMap.comp_assoc]
--   congr 1
--   ext
--   rfl

-- @[coassoc_simps]
-- lemma foo₈_assoc (f : M' →ₗ[R] M) (g : N' →ₗ[R] N ⊗[R] P) (f' : P →ₗ[R] Q) (f'' : N →ₗ[R] Q')
--     (h : P' →ₗ[R] N' ⊗[R] M') :
--     (TensorProduct.comm R _ _).toLinearMap ⊗ₘ f' ∘ₗ
--         α⁻¹ ∘ₗ f'' ⊗ₘ (TensorProduct.comm R _ _).toLinearMap ∘ₗ
--         α ∘ₗ g ⊗ₘ f ∘ₗ h =
--     ((.id ⊗ₘ f'') ⊗ₘ f') ∘ₗ α⁻¹ ∘ₗ (f ⊗ₘ g) ∘ₗ
--       (TensorProduct.comm R _ _).toLinearMap ∘ₗ h := by
--   simp_rw [← LinearMap.comp_assoc]
--   congr 1
--   simp_rw [LinearMap.comp_assoc, foo₈]

@[coassoc_simps]
lemma foo₉ [Coalgebra R M] (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    (g ⊗ₘ (TensorProduct.comm R M N).toLinearMap) ∘ₗ
      α ∘ₗ (((TensorProduct.comm R M M).toLinearMap ∘ₗ δ) ⊗ₘ f) ∘ₗ δ =
    (g ⊗ₘ (f ⊗ₘ .id)) ∘ₗ α ∘ₗ δ ⊗ₘ LinearMap.id ∘ₗ
      (TensorProduct.comm R M M).toLinearMap ∘ₗ δ := by
  rw [← symm_comp_map_assoc, ← LinearMap.lTensor_def, ← Coalgebra.coassoc, ← f.comp_id,
    TensorProduct.map_comp, ← LinearMap.rTensor_def]
  simp only [← LinearMap.comp_assoc]
  congr 2
  ext
  rfl

@[coassoc_simps]
lemma foo₉_assoc [Coalgebra R M] (f : M →ₗ[R] N) (g : M →ₗ[R] P) (h : Q →ₗ[R] M) :
    (g ⊗ₘ (TensorProduct.comm R M N).toLinearMap) ∘ₗ
      (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ
        (((TensorProduct.comm R M M).toLinearMap ∘ₗ δ) ⊗ₘ f) ∘ₗ δ ∘ₗ h =
    (g ⊗ₘ (f ⊗ₘ .id)) ∘ₗ α ∘ₗ δ ⊗ₘ LinearMap.id ∘ₗ
      (TensorProduct.comm R M M).toLinearMap ∘ₗ δ ∘ₗ h := by
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp only [LinearMap.comp_assoc, foo₉]

lemma comp_assoc_symm (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (f₃ : P →ₗ[R] Q) :
    f₃ ∘ₗ (f₂ ∘ₗ f₁) = (f₃ ∘ₗ f₂) ∘ₗ f₁ := by simp only [coassoc_simps]

lemma map_comp_left (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g : M' →ₗ[R] N') :
    map (f₂ ∘ₗ f₁) g = map f₂ .id ∘ₗ map f₁ g := by simp only [coassoc_simps]

lemma map_comp_right (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g : M' →ₗ[R] N') :
    map g (f₂ ∘ₗ f₁) = map .id f₂ ∘ₗ map g f₁ := by simp only [coassoc_simps]

lemma map_comul_right_comp_comul (f : A →ₗ[R] M) :
    map f δ ∘ₗ δ = α ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp only [coassoc_simps]

lemma map_comul_right_comp_comul_assoc (f : A →ₗ[R] M) (h : M ⊗[R] (A ⊗[R] A) →ₗ[R] P) :
    (h ∘ₗ map f δ) ∘ₗ δ = h ∘ₗ α ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp only [coassoc_simps]

lemma map_comp_comul_right_comp_comul (f : A →ₗ[R] M) (g : A ⊗[R] A →ₗ[R] N) :
    map f (g ∘ₗ δ) ∘ₗ δ = M ◁ g ∘ₗ α ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp only [coassoc_simps]

lemma map_comp_comul_right_comp_comul_assoc
    (f : A →ₗ[R] M) (g : A ⊗[R] A →ₗ[R] N) (h : M ⊗[R] N →ₗ[R] P) :
    (h ∘ₗ map f (g ∘ₗ δ)) ∘ₗ δ = h ∘ₗ M ◁ g ∘ₗ α ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
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
    (i ∘ₗ map f (map g h)) ∘ₗ α = i ∘ₗ α ∘ₗ map (map f g) h := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_eq_assoc' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₁ : M' ⊗[R] Q' →ₗ[R] Q) (i₂ : N' ⊗[R] P' →ₗ[R] Q') :
    (i₁ ∘ₗ map f (i₂ ∘ₗ map g h)) ∘ₗ α = i₁ ∘ₗ M' ◁ i₂ ∘ₗ α ∘ₗ map (map f g) h := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_eq_assoc'' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₂ : N' ⊗[R] P' →ₗ[R] Q') :
    map f (i₂ ∘ₗ map g h) ∘ₗ α = M' ◁ i₂ ∘ₗ α ∘ₗ map (map f g) h := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_symm_eq_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i : (M' ⊗[R] N') ⊗[R] P' →ₗ[R] Q) :
    (i ∘ₗ map (map f g) h) ∘ₗ α⁻¹ = i ∘ₗ α⁻¹ ∘ₗ map f (map g h) := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_symm_eq_assoc' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₁ : Q' ⊗[R] P' →ₗ[R] Q) (i₂ : M' ⊗[R] N' →ₗ[R] Q') :
    (i₁ ∘ₗ map (i₂ ∘ₗ map f g) h) ∘ₗ α⁻¹ =
      i₁ ∘ₗ i₂ ▷ P' ∘ₗ α⁻¹ ∘ₗ map f (map g h) := by
  simp only [coassoc_simps]

lemma map_map_comp_assoc_symm_eq_assoc'' (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i₂ : M' ⊗[R] N' →ₗ[R] Q') :
    map (i₂ ∘ₗ map f g) h ∘ₗ α⁻¹ = i₂ ▷ P' ∘ₗ α⁻¹ ∘ₗ map f (map g h) := by
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
