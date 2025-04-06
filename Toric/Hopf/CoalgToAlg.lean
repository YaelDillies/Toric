/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
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

suppress_compilation

variable {R A C : Type*} [CommRing R]

namespace LinearMap
variable [Ring A] [AddCommGroup C] [Algebra R A] [Module R C] [Coalgebra R C]

instance : One (C →ₗ[R] A) where one := Algebra.linearMap R A ∘ₗ counit
instance : Mul (C →ₗ[R] A) where mul f g := mul' R A ∘ₗ TensorProduct.map f g ∘ₗ comul

lemma one_def : (1 : C →ₗ[R] A) = Algebra.linearMap R A ∘ₗ counit := rfl
lemma mul_def (f g : C →ₗ[R] A) : f * g = mul' R A ∘ₗ TensorProduct.map f g ∘ₗ comul := rfl

@[simp] lemma one_apply' (c : C) : (1 : C →ₗ[R] A) c = algebraMap R A (counit c) := rfl

@[simp]
lemma mul_apply'' (f g : C →ₗ[R] A) (c : C) : (f * g) c = mul' R A (.map f g (comul c)) := rfl

local notation "η" => Algebra.linearMap
local notation "ε" => counit
local notation "μ" => mul' R A
local notation "δ" => comul
local infix:70 " ⊗ₘ " => TensorProduct.map
-- local notation "α" => TensorProduct.assoc _ _ _

instance : Ring (C →ₗ[R] A) where
  left_distrib f g h := by ext; simp [TensorProduct.map_add_right]
  right_distrib f g h := by ext; simp [TensorProduct.map_add_left]
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp
  mul_assoc f g h := by
    calc
          μ ∘ₗ (μ ∘ₗ (f ⊗ₘ g) ∘ₗ δ ⊗ₘ h) ∘ₗ δ
      _ = (μ ∘ₗ .rTensor _ μ) ∘ₗ ((f ⊗ₘ g) ⊗ₘ h) ∘ₗ (.rTensor _ δ ∘ₗ δ) := by
        rw [comp_assoc, ← comp_assoc _ _ (rTensor _ _), rTensor_comp_map,
          ← comp_assoc _ (rTensor _ _), map_comp_rTensor, comp_assoc]
      _ = (μ ∘ₗ .lTensor _ μ) ∘ₗ (f ⊗ₘ (g ⊗ₘ h)) ∘ₗ (lTensor C δ ∘ₗ δ) := by
        rw [← coassoc_symm]
        -- What's the `Algebra` equivalent of `coassoc`?
        -- Probably associativity of multiplication :)
        sorry
      _ = μ ∘ₗ (f ⊗ₘ μ ∘ₗ (g ⊗ₘ h) ∘ₗ δ) ∘ₗ δ := by
        rw [comp_assoc, ← comp_assoc _ _ (lTensor _ _), lTensor_comp_map,
          ← comp_assoc _ (lTensor _ _), map_comp_lTensor, comp_assoc]
  one_mul f := by
    stop
    calc
          μ ∘ₗ (η ∘ₗ ε ⊗ₘ f) ∘ₗ δ
      _ = (μ ∘ₗ rTensor _ η) ∘ₗ lTensor _ f ∘ₗ (lTensor _ ε ∘ₗ δ) := sorry
      _ = _ := _
      _ = f := sorry
  mul_one f := by
    stop
    calc
          μ ∘ₗ (f ⊗ₘ η ∘ₗ ε) ∘ₗ δ
      _ = (μ ∘ₗ lTensor _ η) ∘ₗ rTensor _ f ∘ₗ (rTensor _ ε ∘ₗ δ) := sorry
      _ = f := sorry

end LinearMap

namespace BialgHom
variable [CommRing A] [CommRing C] [Bialgebra R A] [Bialgebra R C]

instance : One (C →ₐc[R] A) where one := (unitBialgHom R A).comp <| counitBialgHom R C
instance : Mul (C →ₐc[R] A) where
  mul f g := .comp (mulBialgHom R A) <| .comp sorry <| comulBialgHom R C

lemma one_def : (1 : C →ₐc[R] A) = (unitBialgHom R A).comp (counitBialgHom ..) := rfl
-- lemma mul_def (f g : C →ₐc[R] A) : f * g = mul' R A ∘ₗ TensorProduct.map f g ∘ₗ comul := rfl

@[simp] lemma one_apply' (c : C) : (1 : C →ₐc[R] A) c = algebraMap R A (counit c) := rfl

-- @[simp]
-- lemma mul_apply'' (f g : C →ₐc[R] A) (c : C) : (f * g) c = mul' R A (.map f g (comul c)) := rfl

lemma toLinearMap_one : (1 : C →ₐc[R] A) = (1 : C →ₗ[R] A) := rfl
lemma toLinearMap_mul (f g : C →ₐc[R] A) : ↑(f * g) = (f * g : C →ₗ[R] A) := sorry

-- instance : Ring (C →ₐc[R] A) := coe_linearMap_injective.ring _ _ _ _ _ _ _

end BialgHom
