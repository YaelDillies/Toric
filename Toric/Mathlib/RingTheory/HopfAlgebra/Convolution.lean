/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
import Toric.Mathlib.Algebra.Algebra.Defs
import Toric.Mathlib.RingTheory.Bialgebra.Basic
import Toric.Mathlib.RingTheory.Bialgebra.Convolution
import Toric.Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Convolution product on Hopf algebra maps

This file constructs the ring structure on bialgebra homs `C → A` where `C` and `A` are Hopf
algebras and multiplication is given by
```
         .
        / \
f * g = f g
        \ /
         .
```
-/

suppress_compilation

open Coalgebra Bialgebra TensorProduct

-- TODO: Remove universe monomorphism
-- TODO: Generalise to semirings
universe u
variable {R A C : Type u} [CommRing R]

namespace HopfAlgebra
variable [CommRing A] [HopfAlgebra R A]

lemma antipode_mul_antidistrib (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) b * antipode (R := R) a := by
  let α := antipode ∘ₗ .mul' R A
  let β : A ⊗[R] A →ₗ[R] A := .mul' R A ∘ₗ map antipode antipode ∘ₗ TensorProduct.comm R A A
  suffices α = β from sorry
  apply left_inv_eq_right_inv (M := A ⊗[R] A →ₗ[R] A) (a := LinearMap.mul' R A) <;> ext a b
  · simp [α, ((ℛ R a).tmul (ℛ R b)).mul_apply, ← Bialgebra.counit_mul,
      ((ℛ R a).mul (ℛ R b)).algebraMap_counit_eq_sum_antipode_mul]
  · simp [((ℛ R a).tmul (ℛ R b)).mul_apply, mul_comm, mul_mul_mul_comm,
      Finset.sum_mul_sum, ← Finset.sum_product', α, β, -sum_mul_antipode_eq,
      (ℛ R a).algebraMap_counit_eq_sum_mul_antipode, (ℛ R b).algebraMap_counit_eq_sum_mul_antipode]

lemma antipode_mul_distrib (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) a * antipode (R := R) b := by
  rw [antipode_mul_antidistrib, mul_comm]

alias antipode_mul := antipode_mul_distrib

variable (R A) in
@[simps!]
def antipodeAlgHom : A →ₐ[R] A := .ofLinearMap antipode antipode_one antipode_mul

@[simp] lemma toLinearMap_antipodeAlgHom : (antipodeAlgHom R A).toLinearMap = antipode := rfl

end HopfAlgebra

namespace LinearMap

local notation "η" => Algebra.linearMap R A
local notation "ε" => counit (R := R) (A := C)
local notation "μ" => mul' R A
local notation "δ" => comul
local infix:70 " ⊗ₘ " => TensorProduct.map
-- local notation "α" => TensorProduct.assoc _ _ _

variable [Ring C] [HopfAlgebra R C]

@[simp] lemma antipode_mul_id : antipode (R := R) (A := C) * id = 1 := by
  ext; simp [mul_def, ← LinearMap.rTensor_def]

@[simp] lemma id_mul_antipode : id * antipode (R := R) (A := C) = 1 := by
  ext; simp [mul_def, ← LinearMap.lTensor_def]

lemma counit_comp_antipode : ε ∘ₗ antipode (R := R) (A := C) = ε := calc
  _ = 1 * (ε ∘ₗ antipode (R := R) (A := C)) := (one_mul _).symm
  _ = (ε ∘ₗ id) * (ε ∘ₗ antipode (R := R) (A := C)) := rfl
  _ = (counitAlgHom R C).toLinearMap ∘ₗ (id * antipode (R := R) (A := C)) := by
    simp only [comp_id, comp_mul_distrib]
    simp
  _ = ε ∘ₗ 1 := by simp
  _ = ε := by ext; simp

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
variable [CommRing A] [Ring C] [Bialgebra R C] [HopfAlgebra R A]

lemma antipode_id_cancel : HopfAlgebra.antipodeAlgHom R A * AlgHom.id R A = 1 := by
  apply AlgHom.toLinearMap_injective
  rw [toLinearMap_mul]
  ext
  simp [LinearMap.antipode_mul_id]

lemma counit_comp_antipode :
    (counitAlgHom R A).comp (HopfAlgebra.antipodeAlgHom R A) = counitAlgHom R A := by
  apply AlgHom.toLinearMap_injective
  simp [LinearMap.counit_comp_antipode]

private lemma inv_convMul_cancel (f : C →ₐc[R] A) :
    (.comp (HopfAlgebra.antipodeAlgHom R A) f : C →ₐ[R] A) * f = 1 := calc
  _ = (.comp (HopfAlgebra.antipodeAlgHom R A) f : C →ₐ[R] A) * (.comp (.id R A) f) := by simp
  _ = .comp (.mul R A) (.comp (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R A)
       (.id R A)) <| .comp (Algebra.TensorProduct.map f f) (comulAlgHom R C)) := by
    rw [mul_def, Algebra.TensorProduct.map_comp]
    simp only [comp_assoc]
  _ = (HopfAlgebra.antipodeAlgHom R A * AlgHom.id R A).comp f := by
    simp only [mul_def, BialgHomClass.map_comp_comulAlgHom]
    simp only [comp_assoc]
  _ = _ := by simp [antipode_id_cancel, one_def, comp_assoc]

end AlgHom

namespace BialgHom
variable [CommRing A] [CommRing C]

section HopfAlgebra
variable [HopfAlgebra R A] [HopfAlgebra R C] [IsCocomm R C]

instance : Inv (C →ₐc[R] A) where inv f := sorry

-- lemma inv_def (f : C →ₐc[R] A) : f⁻¹ = sorry := rfl

-- @[simp]
-- lemma inv_apply (f : C →ₐc[R] A) (c : C) : f⁻¹ c = sorry := rfl

private lemma inv_convMul_cancel (f : C →ₐc[R] A) : f⁻¹ * f = 1 := sorry

instance : CommGroup (C →ₐc[R] A) where inv_mul_cancel := inv_convMul_cancel

end HopfAlgebra
end BialgHom
