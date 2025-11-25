/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.RingTheory.Bialgebra.Convolution

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

open Algebra Coalgebra Bialgebra HopfAlgebra TensorProduct
open scoped ConvolutionProduct RingTheory.LinearMap

variable {R A C : Type*} [CommSemiring R]

namespace HopfAlgebra
variable [CommSemiring A] [HopfAlgebra R A]

lemma antipode_mul_antidistrib (a b : A) :
    antipode R (a * b) = antipode R b * antipode R a := by
  let α := antipode R ∘ₗ .mul' R A
  let β : A ⊗[R] A →ₗ[R] A := .mul' R A ∘ₗ map (antipode R) (antipode R) ∘ₗ TensorProduct.comm R A A
  suffices α = β from congr($this (a ⊗ₜ b))
  apply left_inv_eq_right_inv (a := LinearMap.mul' R A) <;> ext a b
  · simp [α, ((ℛ R a).tmul (ℛ R b)).convMul_apply, ← Bialgebra.counit_mul, mul_comm b a,
      ← sum_antipode_mul_eq_algebraMap_counit ((ℛ R a).mul (ℛ R b))]
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply, mul_comm, mul_mul_mul_comm, Finset.sum_mul_sum,
      ← Finset.sum_product', β, ← sum_mul_antipode_eq_algebraMap_counit (ℛ R a),
      ← sum_mul_antipode_eq_algebraMap_counit (ℛ R b)]

lemma antipode_mul_distrib (a b : A) :
    antipode R (a * b) = antipode R a * antipode R b := by
  rw [antipode_mul_antidistrib, mul_comm]

alias antipode_mul := antipode_mul_distrib

variable (R A) in
@[simps!]
def antipodeAlgHom : A →ₐ[R] A := .ofLinearMap (antipode R) antipode_one antipode_mul

@[simp] lemma toLinearMap_antipodeAlgHom : (antipodeAlgHom R A).toLinearMap = antipode R := rfl

end HopfAlgebra

namespace LinearMap

local notation "η" => Algebra.linearMap R A
local notation "ε" => counit (R := R) (A := C)
local notation "μ" => mul' R A
local notation "δ" => comul
local infix:70 " ⊗ₘ " => TensorProduct.map
-- local notation "α" => TensorProduct.assoc _ _ _

variable [Semiring C] [HopfAlgebra R C]

@[simp] lemma antipode_mul_id : antipode R (A := C) * id = 1 := by
  ext; simp [convMul_def, ← LinearMap.rTensor_def]

@[simp] lemma id_mul_antipode : id * antipode R (A := C) = 1 := by
  ext; simp [convMul_def, ← LinearMap.lTensor_def]

@[simp] lemma counit_comp_antipode : ε ∘ₗ antipode R (A := C) = ε := calc
  _ = 1 * (ε ∘ₗ antipode R (A := C)) := (one_mul _).symm
  _ = (ε ∘ₗ id) * (ε ∘ₗ antipode R (A := C)) := rfl
  _ = (counitAlgHom R C).toLinearMap ∘ₗ (id * antipode R (A := C)) := by
    simp only [comp_id, algHom_comp_convMul_distrib]
    simp
  _ = ε ∘ₗ 1 := by simp
  _ = ε := by ext; simp

@[simp] lemma counit_antipode (a : C) : ε (antipode R a) = ε a := congr($counit_comp_antipode a)

end LinearMap

namespace LinearMap
variable [Semiring C] [HopfAlgebra R C]

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
local notation "α" => TensorProduct.assoc R
local notation "β" => TensorProduct.comm R
local notation "𝑺" => antipode R (A := C)
local notation "𝑭" => δ₁ ∘ₗ 𝑺
local notation "𝑮" => (𝑺 ⊗ₘ 𝑺) ∘ₗ (β C C) ∘ₗ δ₁

lemma comul_right_inv : δ₁ * 𝑭 = 1 := calc
    μ₂ ∘ₗ (δ₁ ⊗ₘ (δ₁ ∘ₗ 𝑺)) ∘ₗ δ₁
  _ = μ₂ ∘ₗ ((δ₁ ∘ₗ id) ⊗ₘ (δ₁ ∘ₗ 𝑺)) ∘ₗ δ₁ := rfl
  _ = μ₂ ∘ₗ (δ₁ ⊗ₘ δ₁) ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ₁ := by
    simp only [_root_.TensorProduct.map_comp, comp_assoc]
  _ = δ₁ ∘ₗ μ₁ ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ₁ := by
      have : μ₂ ∘ₗ (δ₁ ⊗ₘ δ₁) = δ₁ ∘ₗ μ₁ := by ext; simp
      simp [this, ← comp_assoc]
  _ = δ₁ ∘ₗ (id * 𝑺) := rfl
  _ = δ₁ ∘ₗ η₁ ∘ₗ ε₁ := by simp [convOne_def]
  _ = η₂ ∘ₗ ε₁ := by
      have : δ₁ ∘ₗ η₁ = η₂ := by ext; simp; rfl
      simp [this, ← comp_assoc]

end LinearMap

namespace AlgHom
variable [CommSemiring A] [Semiring C] [Bialgebra R C] [HopfAlgebra R A]

lemma antipode_id_cancel : HopfAlgebra.antipodeAlgHom R A * AlgHom.id R A = 1 := by
  apply AlgHom.toLinearMap_injective
  rw [toLinearMap_mul]
  ext
  simp [LinearMap.antipode_mul_id]

lemma counit_comp_antipode :
    (counitAlgHom R A).comp (HopfAlgebra.antipodeAlgHom R A) = counitAlgHom R A :=
  AlgHom.toLinearMap_injective <| by simp

private lemma inv_convMul_cancel (f : C →ₐc[R] A) :
    (.comp (HopfAlgebra.antipodeAlgHom R A) f : C →ₐ[R] A) * f = 1 := calc
  _ = (.comp (HopfAlgebra.antipodeAlgHom R A) f : C →ₐ[R] A) * (.comp (.id R A) f) := by simp
  _ = .comp (lmul' R) (.comp (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R A)
       (.id R A)) <| .comp (Algebra.TensorProduct.map f f) (comulAlgHom R C)) := by
    rw [mul_def, Algebra.TensorProduct.map_comp]
    simp only [comp_assoc]
  _ = (HopfAlgebra.antipodeAlgHom R A * AlgHom.id R A).comp f := by
    simp only [mul_def, BialgHomClass.map_comp_comulAlgHom]
    simp only [comp_assoc]
  _ = _ := by simp [antipode_id_cancel, one_def, comp_assoc]

end AlgHom

namespace BialgHom
variable [CommSemiring A] [CommSemiring C]

section HopfAlgebra
variable [HopfAlgebra R A] [HopfAlgebra R C] [IsCocomm R C]

@[coassoc_simps] --todo : add the assoc version
lemma HopfAlgebra.mul_antipode_rTensor_comul'.{u, v} {R : Type u} {A : Type v}
    {_ : CommSemiring R} {_ : Semiring A} [self : HopfAlgebra R A] :
    LinearMap.mul' R A ∘ₗ TensorProduct.map (HopfAlgebraStruct.antipode R) .id ∘ₗ
      CoalgebraStruct.comul = Algebra.linearMap R A ∘ₗ CoalgebraStruct.counit :=
  HopfAlgebra.mul_antipode_rTensor_comul ..

@[coassoc_simps] --todo : add the assoc version
lemma HopfAlgebra.mul_antipode_lTensor_comul'.{u, v} {R : Type u} {A : Type v}
    {_ : CommSemiring R} {_ : Semiring A} [self : HopfAlgebra R A] :
    LinearMap.mul' R A ∘ₗ TensorProduct.map .id (HopfAlgebraStruct.antipode R) ∘ₗ
      CoalgebraStruct.comul = Algebra.linearMap R A ∘ₗ CoalgebraStruct.counit :=
  HopfAlgebra.mul_antipode_lTensor_comul ..


/-- The antipode as a coalgebra hom. -/
def antipodeBialgHom : C →ₐc[R] C where
  __ := antipodeAlgHom R (A := C)
  map_smul' := _
  counit_comp := counit_comp_antipode
  map_comp_comul := by
    apply left_inv_eq_right_inv (a := comul)
    · sorry
    · sorry

instance : Inv (C →ₐc[R] A) where inv := antipodeBialgHom.comp

set_option linter.unusedSectionVars false in
lemma inv_def (f : C →ₐc[R] A) : f⁻¹ = antipodeBialgHom.comp f := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma inv_apply (f : C →ₐc[R] A) (c : C) : f⁻¹ c = antipode R (f c) := rfl

private lemma inv_convMul_cancel (f : C →ₐc[R] A) : f⁻¹ * f = 1 := sorry

instance : CommGroup (C →ₐc[R] A) where inv_mul_cancel := inv_convMul_cancel

end HopfAlgebra
end BialgHom
