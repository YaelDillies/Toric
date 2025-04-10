/-
Copyright (c) 2025 Yaël Dillies, Aaron Liu, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Aaron Liu, Michał Mrugała
-/
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.Algebra.Module.Equiv.Defs
import Toric.Mathlib.LinearAlgebra.TensorProduct.Associator
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Cocommutative coalgebras

This file defines cocommutative coalgebras, namely coalgebras `C` in which the comultiplication
`δ : C → C ⊗ C` commutes with the swapping `β : C ⊗ C ≃ C ⊗ C` of the factors in the tensor
product.
-/

open Coalgebra TensorProduct

universe u

variable {R C : Type u} [CommSemiring R]

namespace Coalgebra
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable (R C) in
class IsCocomm where
  comul_comm' : (TensorProduct.comm R C C).comp (comul (R := R)) = comul (R := R) (A := C)

instance : IsCocomm R R where comul_comm' := by ext; simp

local notation "ε" => counit (R := R) (A := C)
local notation "μ" => LinearMap.mul' R R
local notation "δ" => comul (R := R)
local infix:90 " ◁ " => LinearMap.lTensor
local notation:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local infix:70 " ⊗ₘ " => TensorProduct.map
local notation "α" => TensorProduct.assoc R

local notation "β" => TensorProduct.comm R

variable [IsCocomm R C]

variable (R C) in
@[simp]
lemma comul_comm : (TensorProduct.comm R C C).comp δ = δ := IsCocomm.comul_comm'

/-- Comultiplication as a coalgebra hom. -/
def comulCoalgHom : C →ₗc[R] C ⊗[R] C where
  __ := δ
  counit_comp := calc
        μ ∘ₗ (ε ⊗ₘ ε) ∘ₗ δ
    _ = (μ ∘ₗ ε ▷ R) ∘ₗ (C ◁ ε ∘ₗ δ) := by
      rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ (.rTensor _ _)]; simp
    _ = ε := by ext; simp
  map_comp_comul := by
    rw [instCoalgebraStruct_comul]
    simp only [tensorTensorTensorComm_def, TensorProduct.coe_congr,
      TensorProduct.leftComm_def, LinearEquiv.coe_trans, LinearEquiv.refl_toLinearMap]
    simp only [LinearMap.comp_assoc, ← LinearMap.lTensor_def, ← LinearMap.rTensor_def,
      LinearMap.lTensor_comp]
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.lTensor_tensor]
    simp only [LinearMap.comp_assoc, LinearEquiv.toLinearMap_comp_symm_comp]
    rw [Coalgebra.coassoc]
    conv =>
      enter [2, 2]
      simp only [← LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
      simp only [LinearMap.comp_assoc]
      rw [Coalgebra.coassoc_symm]
      rw [← LinearMap.comp_assoc comul, ← LinearMap.rTensor_comp, comul_comm]
      rw [Coalgebra.coassoc]
    simp only [LinearMap.comp_assoc, LinearMap.lTensor_comp]

end Coalgebra


namespace HopfAlgebra

variable [Semiring C] [HopfAlgebra R C]

variable [IsCocomm R C]

-- Need to refactor CoalgToAlg to use Semirings when possible
def antipodeCoalgHom : C →ₗc[R] C where
  __ := antipode (R := R) (A := C)
  counit_comp := sorry
  map_comp_comul := sorry


end HopfAlgebra
