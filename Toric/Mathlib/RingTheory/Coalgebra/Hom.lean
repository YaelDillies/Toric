import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Toric.Mathlib.LinearAlgebra.TensorProduct.Associator
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic
import Toric.Mathlib.LinearAlgebra.TensorProduct.Tower
import Toric.Mathlib.RingTheory.Coalgebra.Basic

open TensorProduct

namespace Coalgebra
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
    simp only [comul_def, AlgebraTensorModule.tensorTensorTensorComm_eq_tensorTensorTensorComm,
      tensorTensorTensorComm, TensorProduct.coe_congr, TensorProduct.leftComm,
      LinearEquiv.coe_trans, LinearEquiv.refl_toLinearMap, AlgebraTensorModule.map_eq_map]
    simp only [LinearMap.comp_assoc, ← LinearMap.lTensor_def, ← LinearMap.rTensor_def,
      LinearMap.lTensor_comp]
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.lTensor_tensor]
    simp only [LinearMap.comp_assoc, LinearEquiv.comp_symm_cancel_left]
    rw [Coalgebra.coassoc]
    conv =>
      enter [2, 2]
      simp only [LinearEquiv.coe_toLinearMap_one, ← LinearMap.lTensor_def, ← LinearMap.rTensor_def,
        ← LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
      simp only [LinearMap.comp_assoc]
      rw [Coalgebra.coassoc_symm]
      rw [← LinearMap.comp_assoc comul, ← LinearMap.rTensor_comp, comm_comp_comul]
      rw [Coalgebra.coassoc]
    simp only [LinearMap.comp_assoc, LinearMap.lTensor_comp]

end Coalgebra
