/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Toric.Mathlib.RingTheory.Bialgebra.Hom
import Toric.Mathlib.RingTheory.HopfAlgebra.Basic

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

lemma AlgHom.map_comp_mul {B : Type u} [Ring B] [Algebra R B] (h : A →ₐ B) :
    h.toLinearMap ∘ₗ μ = mul' R B ∘ₗ (h.toLinearMap ⊗ₘ h.toLinearMap) := by ext; simp

lemma comp_mul_distrib {B : Type u} [Ring B] [Algebra R B] (f g : C →ₗ[R] A) (h : A →ₐ[R] B) :
    h.toLinearMap.comp (f * g) = (.comp h.toLinearMap f) * (.comp h.toLinearMap g) := by
  simp only [mul_def, map_comp, ← comp_assoc, AlgHom.map_comp_mul]

end Ring

section Antipode
variable [Ring C] [HopfAlgebra R C]

export HopfAlgebraStruct (antipode)

@[simp]
lemma algebraMapBase : Algebra.linearMap R R = id := rfl

lemma toBaseId : ε = 1 := by simp [one_def]

@[simp]
lemma counitAlgHomToLinear: (counitAlgHom R C).toLinearMap = ε := rfl

@[simp]
lemma antipode_id_cancel : antipode (R := R) (A := C) * id = 1 := by
  ext; simp [LinearMap.mul_def, ← LinearMap.rTensor_def]

@[simp]
lemma id_antipode_cancel : id * antipode (R := R) (A := C) = 1 := by
  ext; simp [LinearMap.mul_def, ← LinearMap.lTensor_def]

lemma counit_comp_antipode : ε ∘ₗ (antipode (R := R) (A := C)) = ε := calc
  _ = 1 * (ε ∘ₗ (antipode (R := R) (A := C))) := (one_mul _).symm
  _ = (ε ∘ₗ id) * (ε ∘ₗ (antipode (R := R) (A := C))) := rfl
  _ = (counitAlgHom R C).toLinearMap ∘ₗ (id * (antipode (R := R) (A := C))) := by
    simp only [comp_id, comp_mul_distrib]
    simp
  _ = ε ∘ₗ 1 := by simp
  _ = ε := by ext; simp

end Antipode

section CommRing
variable [CommRing A] [AddCommGroup C] [Algebra R A] [Module R C] [Coalgebra R C]

private lemma convMul_comm (f g : C →ₗ[R] A) : f * g = g * f := calc
      μ ∘ₗ (f ⊗ₘ g) ∘ₗ δ
  _ = μ ∘ₗ (g ⊗ₘ f) ∘ₗ δ := sorry

noncomputable instance : CommRing (C →ₗ[R] A) where
  mul_comm := convMul_comm

end CommRing
end LinearMap

namespace LinearMap
variable [Ring C] [HopfAlgebra R C]

local notation "ε₁" => counit (R := R) (A := C)
local notation "ε₂" => counit (R := R) (A := C ⊗[R] C)
local notation "μ₁" => LinearMap.mul' R C
local notation "μ₂" => LinearMap.mul' R (C ⊗[R] C)
local notation "δ₁" => comul (R := R) (A := C)
local notation "δ₂" => comul (R := R) (A := C ⊗[R] C)
local notation "η₁" => Algebra.linearMap R C
local notation "η₂" => Algebra.linearMap R (C ⊗[R] C)
local infix:90 " ◁ " => LinearMap.lTensor
local notation:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local infix:70 " ⊗ₘ " => TensorProduct.map
local notation "α" => TensorProduct.assoc R
local notation "β" => TensorProduct.comm R
local notation "𝑺" => antipode (R := R) (A := C)
local notation "𝑭" => δ₁ ∘ₗ 𝑺
local notation "𝑮" => (𝑺 ⊗ₘ 𝑺) ∘ₗ (β C C) ∘ₗ δ₁

lemma comul_right_inv : δ₁ * 𝑭 = 1 := calc
    μ₂ ∘ₗ (δ₁ ⊗ₘ (δ₁ ∘ₗ 𝑺)) ∘ₗ δ₁
  _ = μ₂ ∘ₗ ((δ₁ ∘ₗ id) ⊗ₘ (δ₁ ∘ₗ 𝑺)) ∘ₗ δ₁ := rfl
  _ = μ₂ ∘ₗ (δ₁ ⊗ₘ δ₁) ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ₁ := by simp only [map_comp, comp_assoc]
  _ = δ₁ ∘ₗ μ₁ ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ₁ := by
      have : μ₂ ∘ₗ (δ₁ ⊗ₘ δ₁) = δ₁ ∘ₗ μ₁ := by ext; simp
      simp [this, ← comp_assoc]
  _ = δ₁ ∘ₗ (id * 𝑺) := rfl
  _ = δ₁ ∘ₗ η₁ ∘ₗ ε₁ := by simp [one_def]
  _ = η₂ ∘ₗ ε₁ := by
      have : δ₁ ∘ₗ η₁ = η₂ := by ext; simp; rfl
      simp [this, ← comp_assoc]

end LinearMap

namespace AlgHom
variable [CommRing A] [Ring C] [Bialgebra R C]

section BialgebraToAlgebra
variable [Algebra R A]

noncomputable instance : One (C →ₐ[R] A) where one := (Algebra.ofId R A).comp <| counitAlgHom R C
noncomputable instance : Mul (C →ₐ[R] A) where
  mul f g := .comp (mulAlgHom R A) <| .comp (Algebra.TensorProduct.map f g) <| comulAlgHom R C

noncomputable instance : Pow (C →ₐ[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩

lemma one_def : (1 : C →ₐ[R] A) = (Algebra.ofId R A).comp (counitAlgHom ..) := rfl
lemma mul_def (f g : C →ₐ[R] A) : f * g =
    (.comp (mulAlgHom R A) <| .comp (Algebra.TensorProduct.map f g) <| comulAlgHom R C) := rfl

lemma pow_succ (f : C →ₐ[R] A) (n : ℕ) : f ^ (n + 1) = (f ^ n) * f := rfl

@[simp] lemma one_apply' (c : C) : (1 : C →ₐ[R] A) c = algebraMap R A (counit c) := rfl

lemma toLinearMap_one : (1 : C →ₐ[R] A) = (1 : C →ₗ[R] A) := rfl
lemma toLinearMap_mul (f g : C →ₐ[R] A) : (f * g).toLinearMap = f.toLinearMap * g.toLinearMap := rfl
lemma toLinearMap_pow (f : C →ₐ[R] A) (n : ℕ) : (f ^ n).toLinearMap = f.toLinearMap ^ n := by
  induction' n with n hn
  · rfl
  simp only [pow_succ, toLinearMap_mul, hn, _root_.pow_succ]

noncomputable instance : CommMonoid (C →ₐ[R] A) :=
  toLinearMap_injective.commMonoid _ toLinearMap_one toLinearMap_mul toLinearMap_pow

lemma mul_distrib_comp {B : Type u} [Ring B] [Bialgebra R B] (f g : C →ₐ A) (h : B →ₐc[R] C) :
    AlgHom.comp (f * g) (h : B →ₐ[R] C) = (.comp f h) * (.comp g h) := calc
  _ = (.comp (mulAlgHom R A) <| .comp (Algebra.TensorProduct.map f g) <|
      .comp (Algebra.TensorProduct.map (h : B →ₐ[R] C) (h : B →ₐ[R] C)) (comulAlgHom R B)) := by
    simp [mul_def, comp_assoc]
  _ = (.comp (mulAlgHom R A) <|
      .comp (Algebra.TensorProduct.map (.comp f h) (.comp g h)) (comulAlgHom R B)) := by
    rw [Algebra.TensorProduct.map_comp]
    simp [comp_assoc]
  _ = _ := by simp [mul_def]

lemma comp_mul_distrib {B : Type u} [CommRing B] [Algebra R B] (f g : C →ₐ[R] A) (h : A →ₐ[R] B) :
    h.comp (f * g) = (h.comp f) * (h.comp g) := by
  apply toLinearMap_injective
  simp [toLinearMap_mul, LinearMap.comp_mul_distrib]

end BialgebraToAlgebra

section BialgebraToHopfAlgebra
variable [HopfAlgebra R A]

export HopfAlgebraStruct (antipode)

@[simp]
lemma toLinearMap_antipode :
    (HopfAlgebra.antipodeAlgHom R A).toLinearMap = antipode (R := R) (A := A) := rfl

lemma antipode_id_cancel : HopfAlgebra.antipodeAlgHom R A * AlgHom.id R A = 1 := by
  apply AlgHom.toLinearMap_injective
  rw [toLinearMap_mul]
  ext
  simp [LinearMap.antipode_id_cancel]

lemma counit_comp_antipode :
    (counitAlgHom R A).comp (HopfAlgebra.antipodeAlgHom R A) = (counitAlgHom R A) := by
  apply AlgHom.toLinearMap_injective
  simp [LinearMap.counit_comp_antipode]

private lemma inv_convMul_cancel (f : C →ₐc[R] A) :
    (.comp (HopfAlgebra.antipodeAlgHom R A) f) * (f : C →ₐ[R] A) = 1 := calc
  _ = (.comp (HopfAlgebra.antipodeAlgHom R A) f) * (.comp (AlgHom.id R A) (f : C →ₐ[R] A)) := by
    simp
  _ = (.comp (mulAlgHom R A) <|
      .comp (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R A) (AlgHom.id R A)) <|
      .comp (Algebra.TensorProduct.map f f) (comulAlgHom R C)) := by
    rw [mul_def, Algebra.TensorProduct.map_comp]
    simp only [comp_assoc]
  _ = (HopfAlgebra.antipodeAlgHom R A * AlgHom.id R A).comp f := by
    simp only [mul_def, BialgHomClass.map_comp_comulAlgHom]
    simp only [comp_assoc]
  _ = _ := by simp [antipode_id_cancel, one_def, comp_assoc]

end BialgebraToHopfAlgebra

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

lemma pow_succ (f : C →ₐc[R] A) (n : ℕ) : f ^ (n + 1) = (f ^ n) * f := rfl

@[simp] lemma one_apply' (c : C) : (1 : C →ₐc[R] A) c = algebraMap R A (counit c) := rfl

-- @[simp]
-- lemma mul_apply'' (f g : C →ₐc[R] A) (c : C) : (f * g) c = mul' R A (.map f g (comul c)) := rfl

lemma toLinearMap_one : (1 : C →ₐc[R] A).toLinearMap = (1 : C →ₗ[R] A) := rfl
lemma toLinearMap_mul (f g : C →ₐc[R] A) :
    (f * g).toLinearMap = f.toLinearMap * g.toLinearMap := rfl
lemma toLinearMap_pow (f : C →ₐc[R] A) (n : ℕ) : (f ^ n).toLinearMap = f.toLinearMap ^ n := by
  induction' n with n hn
  · rfl
  rw [pow_succ, _root_.pow_succ, toLinearMap_mul, hn]

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
