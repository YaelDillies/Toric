/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Toric.Mathlib.RingTheory.Coalgebra.Basic
import Toric.Mathlib.RingTheory.Coalgebra.CoassocSimps

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
-/

suppress_compilation

open Coalgebra TensorProduct

variable {R A B C : Type*} [CommSemiring R]

namespace LinearMap

local notation "η" => Algebra.linearMap R A
local notation "ε" => counit (R := R) (A := C)
local notation "μ" => mul' R A
local notation "δ" => comul
local infix:70 " ⊗ₘ " => TensorProduct.map
-- local notation "α" => TensorProduct.assoc _ _ _

section Semiring
variable [Semiring A] [Semiring B] [AddCommMonoid C] [Algebra R A] [Algebra R B] [Module R C]
  [Coalgebra R C]

instance instOne : One (C →ₗ[R] A) where one := Algebra.linearMap R A ∘ₗ counit
instance instMul : Mul (C →ₗ[R] A) where mul f g := μ ∘ₗ TensorProduct.map f g ∘ₗ comul

lemma one_def : (1 : C →ₗ[R] A) = Algebra.linearMap R A ∘ₗ counit := rfl
lemma mul_def (f g : C →ₗ[R] A) : f * g = μ ∘ₗ TensorProduct.map f g ∘ₗ comul := rfl

@[simp] lemma one_apply (c : C) : (1 : C →ₗ[R] A) c = algebraMap R A (counit c) := rfl
@[simp] lemma mul_apply (f g : C →ₗ[R] A) (c : C) : (f * g) c = μ (.map f g (comul c)) := rfl

lemma _root_.Coalgebra.Repr.mul_apply {a : C} (𝓡 : Coalgebra.Repr R a) (f g : C →ₗ[R] A) :
    (f * g) a = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  simp [mul_def, ← 𝓡.eq]

private lemma convMul_assoc (f g h : C →ₗ[R] A) : f * g * h = f * (g * h) := by
  trans (((μ ∘ₗ (id ⊗ₘ μ)) ∘ₗ ↑(TensorProduct.assoc R A A A)) ∘ₗ ((f ⊗ₘ g) ∘ₗ δ ⊗ₘ h)) ∘ₗ δ
  · simp only [mul_def, map_comp_left, ← LinearMap.comp_assoc]
    congr 3
    ext
    exact mul_assoc _ _ _
  · simp [mul_def, coassoc_simps]

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

instance : Semiring (C →ₗ[R] A) where
  left_distrib f g h := by ext; simp [TensorProduct.map_add_right]
  right_distrib f g h := by ext; simp [TensorProduct.map_add_left]
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp
  mul_assoc := convMul_assoc
  one_mul := one_convMul
  mul_one := convMul_one

lemma _root_.AlgHom.map_comp_mul (h : A →ₐ B) :
    h.toLinearMap ∘ₗ μ = mul' R B ∘ₗ (h.toLinearMap ⊗ₘ h.toLinearMap) := by ext; simp

lemma comp_mul_distrib (f g : C →ₗ[R] A) (h : A →ₐ[R] B) :
    h.toLinearMap.comp (f * g) = (.comp h.toLinearMap f) * (.comp h.toLinearMap g) := by
  simp only [mul_def, map_comp, ← comp_assoc, AlgHom.map_comp_mul]

end Semiring

section CommSemiring
variable [CommSemiring A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C]
  [IsCocomm R C]

private lemma convMul_comm (f g : C →ₗ[R] A) : f * g = g * f := by
  rw [mul_def, ← comm_comp_comul, ← LinearMap.comp_assoc δ, map_comp_comm_eq, mul_def,
    ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
  congr 3
  ext; exact mul_comm _ _

instance : CommSemiring (C →ₗ[R] A) where
  mul_comm := convMul_comm

end CommSemiring

section Ring
variable [Ring A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C]

instance : Ring (C →ₗ[R] A) where

end Ring

section CommRing
variable [CommRing A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C] [IsCocomm R C]

instance : CommRing (C →ₗ[R] A) where

end CommRing
end LinearMap
