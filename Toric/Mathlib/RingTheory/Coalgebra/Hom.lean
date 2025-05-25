import Mathlib.RingTheory.Coalgebra.Hom
import Toric.Mathlib.Algebra.Module.Equiv.Defs
import Toric.Mathlib.LinearAlgebra.TensorProduct.Associator
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic
import Toric.Mathlib.RingTheory.Coalgebra.Basic

open TensorProduct

namespace Coalgebra
variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [IsCocomm R C]

local notation "ε" => counit (R := R) (A := C)
local notation "μ" => LinearMap.mul' R R
local notation "δ" => comul (R := R)
local infix:90 " ◁ " => LinearMap.lTensor
local notation:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local infix:70 " ⊗ₘ " => TensorProduct.map
local notation "α" => TensorProduct.assoc R

variable (R C) in
/-- Comultiplication as a coalgebra hom. -/
noncomputable def comulCoalgHom : C →ₗc[R] C ⊗[R] C where
  __ := δ
  counit_comp := calc
        μ ∘ₗ (ε ⊗ₘ ε) ∘ₗ δ
    _ = (μ ∘ₗ ε ▷ R) ∘ₗ (C ◁ ε ∘ₗ δ) := by
      rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ (.rTensor _ _)]; simp
    _ = ε := by ext; simp
  map_comp_comul := by
    simp only [comul_def, tensorTensorTensorComm, TensorProduct.coe_congr,
      TensorProduct.leftComm, LinearEquiv.coe_trans, LinearEquiv.refl_toLinearMap]
    simp only [LinearMap.comp_assoc, ← LinearMap.lTensor_def, ← LinearMap.rTensor_def,
      LinearMap.lTensor_comp]
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.lTensor_tensor]
    simp only [LinearMap.comp_assoc, LinearEquiv.toLinearMap_comp_symm_comp]
    rw [Coalgebra.coassoc]
    conv =>
      enter [2, 2]
      simp only [LinearEquiv.coe_toLinearMap_one, ← LinearMap.lTensor_def, ← LinearMap.rTensor_def,
        ← LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
      simp only [LinearMap.comp_assoc]
      rw [Coalgebra.coassoc_symm]
      rw [← LinearMap.comp_assoc comul, ← LinearMap.rTensor_comp, comul_comm]
      rw [Coalgebra.coassoc]
    simp only [LinearMap.comp_assoc, LinearMap.lTensor_comp]

end Coalgebra
