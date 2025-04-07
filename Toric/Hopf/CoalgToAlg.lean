/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
import Mathlib
import Toric.Mathlib.RingTheory.Bialgebra.Hom

/-!
# Convolution product on linear maps from a coalgebra to an algebra

This file constructs the ring structure on linear maps `C → A` where `C` is a coalgebra and `A` an
algebra, where multiplication is given by
```
         .
        / \
f * g = f g
        \ /
         .
```

We then inherit this structure on bialgebra maps `C → A` where `C` and `A` are bialgebras.
-/

open Coalgebra Bialgebra TensorProduct

universe u

variable {R A C : Type u} [CommRing R]

namespace LinearMap

local notation "η" => Algebra.linearMap R A
local notation "ε" => counit (R := R) (A := C)
local notation "μ" => mul' R A
local notation "δ" => comul
local infix:70 " ⊗ₘ " => TensorProduct.map
-- local notation "α" => TensorProduct.assoc _ _ _

section Ring
variable [Ring A] [AddCommGroup C] [Algebra R A] [Module R C] [Coalgebra R C]

instance : One (C →ₗ[R] A) where one := Algebra.linearMap R A ∘ₗ counit
noncomputable instance : Mul (C →ₗ[R] A) where mul f g := mul' R A ∘ₗ TensorProduct.map f g ∘ₗ comul

lemma one_def : (1 : C →ₗ[R] A) = Algebra.linearMap R A ∘ₗ counit := rfl
lemma mul_def (f g : C →ₗ[R] A) : f * g = mul' R A ∘ₗ TensorProduct.map f g ∘ₗ comul := rfl

@[simp] lemma one_apply' (c : C) : (1 : C →ₗ[R] A) c = algebraMap R A (counit c) := rfl

@[simp]
lemma mul_apply'' (f g : C →ₗ[R] A) (c : C) : (f * g) c = mul' R A (.map f g (comul c)) := rfl

private lemma convMul_assoc (f g h : C →ₗ[R] A) : f * g * h = f * (g * h) := calc
      μ ∘ₗ (μ ∘ₗ (f ⊗ₘ g) ∘ₗ δ ⊗ₘ h) ∘ₗ δ
  _ = (μ ∘ₗ .rTensor _ μ) ∘ₗ ((f ⊗ₘ g) ⊗ₘ h) ∘ₗ (.rTensor _ δ ∘ₗ δ) := by
    rw [comp_assoc, ← comp_assoc _ _ (rTensor _ _), rTensor_comp_map,
      ← comp_assoc _ (rTensor _ _), map_comp_rTensor, comp_assoc]
  _ = (μ ∘ₗ rTensor _ μ)
      ∘ₗ (((f ⊗ₘ g) ⊗ₘ h) ∘ₗ (TensorProduct.assoc R C C C).symm) ∘ₗ lTensor C δ ∘ₗ δ := by
    simp only [comp_assoc, coassoc_symm]
  _ = (μ ∘ₗ rTensor A μ ∘ₗ ↑(TensorProduct.assoc R A A A).symm)
      ∘ₗ (f ⊗ₘ (g ⊗ₘ h)) ∘ₗ lTensor C δ ∘ₗ δ := by
    simp only [map_map_comp_assoc_symm_eq, comp_assoc]
  _ = (μ ∘ₗ .lTensor _ μ) ∘ₗ (f ⊗ₘ (g ⊗ₘ h)) ∘ₗ (lTensor C δ ∘ₗ δ) := by
    congr 1
    ext
    simp [mul_assoc]
  _ = μ ∘ₗ (f ⊗ₘ μ ∘ₗ (g ⊗ₘ h) ∘ₗ δ) ∘ₗ δ := by
    rw [comp_assoc, ← comp_assoc _ _ (lTensor _ _), lTensor_comp_map,
      ← comp_assoc _ (lTensor _ _), map_comp_lTensor, comp_assoc]

private lemma one_convMul (f : C →ₗ[R] A) : 1 * f = f := calc
      μ ∘ₗ ((η ∘ₗ ε) ⊗ₘ f) ∘ₗ δ
  _ = μ ∘ₗ ((η ⊗ₘ f) ∘ₗ rTensor C ε) ∘ₗ δ  := by simp only [map_comp_rTensor]
  _ = μ ∘ₗ (η ⊗ₘ f) ∘ₗ (rTensor C ε) ∘ₗ δ := by rw [comp_assoc]
  _ = μ ∘ₗ (rTensor A η ∘ₗ lTensor R f) ∘ₗ rTensor C ε ∘ₗ δ := by simp
  _ = (μ ∘ₗ rTensor A η) ∘ₗ lTensor R f ∘ₗ (rTensor C ε ∘ₗ δ) := by simp only [comp_assoc]
  _ = (μ ∘ₗ rTensor A η) ∘ₗ lTensor R f ∘ₗ ((TensorProduct.mk R R C) 1) := by
    rw [rTensor_counit_comp_comul]
  _ = f := by ext; simp

private lemma convMul_one (f : C →ₗ[R] A) : f * 1 = f := calc
      μ ∘ₗ (f ⊗ₘ (η ∘ₗ ε)) ∘ₗ δ
  _ = μ ∘ₗ ((f ⊗ₘ η) ∘ₗ lTensor C ε) ∘ₗ δ  := by simp only [map_comp_lTensor]
  _ = μ ∘ₗ (f ⊗ₘ η) ∘ₗ lTensor C ε ∘ₗ δ := by rw [comp_assoc]
  _ = μ ∘ₗ (lTensor A η ∘ₗ rTensor R f) ∘ₗ lTensor C ε ∘ₗ δ := by simp
  _ = (μ ∘ₗ lTensor A η) ∘ₗ rTensor R f ∘ₗ (lTensor C ε ∘ₗ δ) := by simp only [comp_assoc]
  _ = (μ ∘ₗ lTensor A η) ∘ₗ rTensor R f ∘ₗ ((TensorProduct.mk R C R).flip 1) := by
    rw [lTensor_counit_comp_comul]
  _ = f := by ext; simp

noncomputable instance : Ring (C →ₗ[R] A) where
  left_distrib f g h := by ext; simp [TensorProduct.map_add_right]
  right_distrib f g h := by ext; simp [TensorProduct.map_add_left]
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp
  mul_assoc := convMul_assoc
  one_mul := one_convMul
  mul_one := convMul_one

end Ring

section CommRing
variable [CommRing A] [AddCommGroup C] [Algebra R A] [Module R C] [Coalgebra R C]

private lemma convMul_comm (f g : C →ₗ[R] A) : f * g = g * f := calc
      μ ∘ₗ (f ⊗ₘ g) ∘ₗ δ
  _ = μ ∘ₗ (g ⊗ₘ f) ∘ₗ δ := sorry

noncomputable instance : CommRing (C →ₗ[R] A) where
  mul_comm := convMul_comm

end CommRing
end LinearMap

namespace AlgHom
variable [CommRing A] [Ring C]

section BialgebraToAlgebra
variable [Algebra R A] [Bialgebra R C]

noncomputable instance : One (C →ₐ[R] A) where one := (Algebra.ofId R A).comp <| counitAlgHom R C
noncomputable instance : Mul (C →ₐ[R] A) where
  mul f g := .comp (mulAlgHom R A) <| .comp (Algebra.TensorProduct.map f g) <| comulAlgHom R C

noncomputable instance : Pow (C →ₐ[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩

lemma one_def : (1 : C →ₐ[R] A) = (Algebra.ofId R A).comp (counitAlgHom ..) := rfl
lemma mul_def (f g : C →ₐ[R] A) : f * g =
    (.comp (mulAlgHom R A) <| .comp (Algebra.TensorProduct.map f g) <| comulAlgHom R C) := rfl

@[simp] lemma one_apply' (c : C) : (1 : C →ₐ[R] A) c = algebraMap R A (counit c) := rfl

lemma toLinearMap_one : (1 : C →ₐ[R] A) = (1 : C →ₗ[R] A) := rfl
lemma toLinearMap_mul (f g : C →ₐ[R] A) : ↑(f * g) = (f * g : C →ₗ[R] A) := rfl
lemma toLinearMap_pow (f : C →ₐ[R] A) (n : ℕ) : ↑(f ^ n) = (f ^ n : C →ₗ[R] A) := sorry

noncomputable instance : CommMonoid (C →ₐ[R] A) := sorry
  --coe_linearMap_injective.commMonoid _ toLinearMap_one toLinearMap_mul toLinearMap_pow

end BialgebraToAlgebra

end AlgHom

namespace BialgHom
variable [CommRing A] [CommRing C]

section Bialgebra
variable [Bialgebra R A] [Bialgebra R C]

instance : One (C →ₐc[R] A) where one := (unitBialgHom R A).comp <| counitBialgHom R C
noncomputable instance : Mul (C →ₐc[R] A) where
  mul f g := .comp (mulBialgHom R A) <| .comp (Bialgebra.TensorProduct.map f g) <| comulBialgHom R C

noncomputable instance : Pow (C →ₐc[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩

lemma one_def : (1 : C →ₐc[R] A) = (unitBialgHom R A).comp (counitBialgHom ..) := rfl
lemma mul_def (f g : C →ₐc[R] A) : f * g =
    (.comp (mulBialgHom R A) <| .comp (Bialgebra.TensorProduct.map f g) <| comulBialgHom R C) := rfl

@[simp] lemma one_apply' (c : C) : (1 : C →ₐc[R] A) c = algebraMap R A (counit c) := rfl

-- @[simp]
-- lemma mul_apply'' (f g : C →ₐc[R] A) (c : C) : (f * g) c = mul' R A (.map f g (comul c)) := rfl

lemma toLinearMap_one : (1 : C →ₐc[R] A) = (1 : C →ₗ[R] A) := rfl
lemma toLinearMap_mul (f g : C →ₐc[R] A) : ↑(f * g) = (f * g : C →ₗ[R] A) := rfl
lemma toLinearMap_pow (f : C →ₐc[R] A) (n : ℕ) : ↑(f ^ n) = (f ^ n : C →ₗ[R] A) := sorry

noncomputable instance : CommMonoid (C →ₐc[R] A) :=
  coe_linearMap_injective.commMonoid _ toLinearMap_one toLinearMap_mul toLinearMap_pow

end Bialgebra

section HopfAlgebra
variable [HopfAlgebra R A] [HopfAlgebra R C]

instance : Inv (C →ₐc[R] A) where inv f := sorry

-- lemma inv_def (f : C →ₐc[R] A) : f⁻¹ = sorry := rfl

-- @[simp]
-- lemma inv_apply (f : C →ₐc[R] A) (c : C) : f⁻¹ c = sorry := rfl

private lemma inv_convMul_cancel (f : C →ₐc[R] A) : f⁻¹ * f = 1 := sorry

noncomputable instance : CommGroup (C →ₐc[R] A) where inv_mul_cancel := inv_convMul_cancel

end HopfAlgebra
end BialgHom
