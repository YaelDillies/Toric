import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Toric.Mathlib.RingTheory.Coalgebra.SimpAttr
import Toric.Mathlib.LinearAlgebra.TensorProduct.Associator
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic
import Toric.Mathlib.LinearAlgebra.TensorProduct.Tower
import Toric.Mathlib.RingTheory.Coalgebra.Basic

open TensorProduct

namespace Coalgebra

section

variable {R A M N P M' N' P' Q : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [Coalgebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q]

local notation3 "α" => _root_.TensorProduct.assoc R
local infix:90 " ◁ " => LinearMap.lTensor
local notation3:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local notation3 "δ" => comul (R := R)

@[coassoc_simps, coassoc_cleanup_simps]
lemma comp_assoc_symm (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (f₃ : P →ₗ[R] Q) :
    f₃ ∘ₗ (f₂ ∘ₗ f₁) = (f₃ ∘ₗ f₂) ∘ₗ f₁ := rfl

@[coassoc_cleanup_simps]
lemma map_comp_left (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g : M' →ₗ[R] N') :
    map (f₂ ∘ₗ f₁) g = map f₂ .id ∘ₗ map f₁ g := by ext; rfl

@[coassoc_cleanup_simps]
lemma map_comp_right (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g : M' →ₗ[R] N') :
    map g (f₂ ∘ₗ f₁) = map .id f₂ ∘ₗ map g f₁ := by ext; rfl

@[coassoc_simps]
lemma map_comul_right_comp_comul (f : A →ₗ[R] M) :
    map f δ ∘ₗ δ = α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc, ← coassoc_symm]
  simp only [← LinearMap.comp_assoc, LinearMap.lTensor_comp_rTensor,
    ← LinearMap.rTensor_comp_lTensor]
  congr; ext; rfl

@[coassoc_simps]
lemma map_comul_right_comp_comul_assoc
    (f : A →ₗ[R] M) (h : M ⊗[R] A ⊗[R] A →ₗ[R] P) :
    (h ∘ₗ map f δ) ∘ₗ δ = h ∘ₗ α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp [LinearMap.comp_assoc, map_comul_right_comp_comul]

@[coassoc_simps]
lemma map_comp_comul_right_comp_comul (f : A →ₗ[R] M) (g : A ⊗[R] A →ₗ[R] N) :
    map f (g ∘ₗ δ) ∘ₗ δ = M ◁ g ∘ₗ α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp [map_comp_right, LinearMap.comp_assoc, map_comul_right_comp_comul]
  rfl

@[coassoc_simps]
lemma map_comp_comul_right_comp_comul_assoc
    (f : A →ₗ[R] M) (g : A ⊗[R] A →ₗ[R] N) (h : M ⊗[R] N →ₗ[R] P) :
    (h ∘ₗ map f (g ∘ₗ δ)) ∘ₗ δ = h ∘ₗ M ◁ g ∘ₗ α M A A ∘ₗ (f ▷ A) ▷ A ∘ₗ δ ▷ A ∘ₗ δ := by
  simp [LinearMap.comp_assoc, map_comp_comul_right_comp_comul]

@[coassoc_simps]
lemma map_map (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g₁ : M' →ₗ[R] N') (g₂ : N' →ₗ[R] P') :
    map f₂ g₂ ∘ₗ map f₁ g₁ = map (f₂ ∘ₗ f₁) (g₂ ∘ₗ g₁) := by
  ext; rfl

@[coassoc_simps]
lemma map_map_assoc (f₁ : M →ₗ[R] N) (f₂ : N →ₗ[R] P) (g₁ : M' →ₗ[R] N') (g₂ : N' →ₗ[R] P')
    (h : P ⊗[R] P' →ₗ[R] Q) :
    (h ∘ₗ map f₂ g₂) ∘ₗ map f₁ g₁ = h ∘ₗ map (f₂ ∘ₗ f₁) (g₂ ∘ₗ g₁) := by
  ext; rfl

@[coassoc_simps]
lemma map_id_id : map (.id) (.id) = (.id : M ⊗[R] N →ₗ[R] _) := by ext; rfl

@[coassoc_simps]
lemma map_map_comp_assoc_eq_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i : M' ⊗[R] N' ⊗[R] P' →ₗ[R] Q) :
    (i ∘ₗ map f (map g h)) ∘ₗ α M N P = i ∘ₗ α M' N' P' ∘ₗ map (map f g) h := by ext; rfl

@[coassoc_simps]
lemma map_map_comp_assoc_symm_eq_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P')
    (i : (M' ⊗[R] N') ⊗[R] P' →ₗ[R] Q) :
    (i ∘ₗ map (map f g) h) ∘ₗ (α M N P).symm = i ∘ₗ (α M' N' P').symm ∘ₗ map f (map g h) := by
  ext; rfl

attribute [coassoc_simps] LinearMap.comp_id LinearMap.id_comp
  LinearMap.lTensor_def LinearMap.rTensor_def map_map_comp_assoc_eq map_map_comp_assoc_symm_eq
  map_id_id AlgebraTensorModule.map_eq_map

open Lean.Parser.Tactic in
/-- `hopf_tensor_induction x with x₁ x₂` attempts to replace `x` by
`x₁ ⊗ₜ x₂` via linearity. This is an implementation detail that is used to set up tensor products
of coalgebras, bialgebras, and hopf algebras, and shouldn't be relied on downstream. -/
scoped macro "coassoc_simps" : tactic =>
  `(tactic|
    ( simp only [coassoc_simps]
      simp only [coassoc_cleanup_simps]
      repeat congr 1; guard_goal_nums 1
      ext; rfl))

end


variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [IsCocomm R C]

local notation3 "ε" => counit (R := R) (A := C)
local notation3 "μ" => LinearMap.mul' R R
local notation3 "δ" => comul (R := R)
local infix:90 " ◁ " => LinearMap.lTensor
local notation3:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local infix:70 " ⊗ₘ " => _root_.TensorProduct.map
local notation3 "α" => _root_.TensorProduct.assoc R
local notation "ββ" => TensorProduct.tensorTensorTensorComm R C C C C

variable (R C) in
/-- Comultiplication as a coalgebra hom. -/
noncomputable def comulCoalgHom : C →ₗc[R] C ⊗[R] C where
  __ := δ
  counit_comp := by
    simp only [counit_def, AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
    calc
        (μ ∘ₗ (ε ⊗ₘ ε)) ∘ₗ δ
    _ = (μ ∘ₗ ε ▷ R) ∘ₗ (C ◁ ε ∘ₗ δ) := by
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ (.rTensor _ _)]
      simp
    _ = ε := by ext; simp
  map_comp_comul := by
    let e : (C ⊗[R] C) ⊗[R] (C ⊗[R] C) ≃ₗ[R] C ⊗[R] (C ⊗[R] C) ⊗[R] C :=
      _root_.TensorProduct.assoc _ _ _ _ ≪≫ₗ
        TensorProduct.congr (.refl _ _) (_root_.TensorProduct.assoc _ _ _ _).symm
    rw [← e.comp_toLinearMap_eq_iff, TensorProduct.comul_def]
    trans (((TensorProduct.comm _ _ _).toLinearMap ∘ₗ δ).rTensor _ ∘ₗ δ).lTensor _ ∘ₗ δ
    · rw [Coalgebra.comm_comp_comul]
      coassoc_simps
    · coassoc_simps

end Coalgebra
