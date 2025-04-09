import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.LinearAlgebra.TensorProduct.Associator

open Coalgebra TensorProduct

universe u

variable {R C : Type u} [CommSemiring R]

namespace Coalgebra
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable (R C) in
class IsCocomm where
  comul_comm' : (TensorProduct.comm R C C).comp (comul (R := R)) = comul (R := R) (A := C)

instance : IsCocomm R R where comul_comm' := by ext; simp

variable [IsCocomm R C]

local notation "ε" => counit (R := R) (A := C)
local notation "μ" => LinearMap.mul' R R
local infix:90 " ◁ " => LinearMap.lTensor
local notation:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local notation "δ" => comul (R := R)
local infix:70 " ⊗ₘ " => TensorProduct.map
local notation "α" => TensorProduct.assoc R

local notation "β" => TensorProduct.comm R

variable (R C) in
@[simp]
lemma comul_comm : (TensorProduct.comm R C C).comp δ = δ := IsCocomm.comul_comm'

private lemma gigaDiagram :
    (α C C (C ⊗ C)).symm.toLinearMap
     ∘ₗ C ◁ (α C C C).toLinearMap
     ∘ₗ C ◁ (δ ▷ C)
     ∘ₗ C ◁ δ
     ∘ₗ δ
       = (δ ⊗ₘ δ)
         ∘ₗ δ := calc
   _ = (α _ _ _).symm.toLinearMap
         ∘ₗ C ◁ ((α _ _ _).toLinearMap ∘ₗ δ ▷ C ∘ₗ δ)
         ∘ₗ δ := by simp [LinearMap.lTensor_comp, LinearMap.comp_assoc]
   _ = (α _ _ _).symm.toLinearMap
         ∘ₗ C ◁ (C ◁ δ)
         ∘ₗ C ◁ δ
         ∘ₗ δ := by simp [coassoc, LinearMap.lTensor_comp, LinearMap.comp_assoc]
   _ = ((C ⊗ C) ◁ δ
         ∘ₗ (α _ _ _).symm.toLinearMap)
         ∘ₗ C ◁ δ
         ∘ₗ δ := by simp [LinearMap.lTensor_tensor, LinearMap.comp_assoc]
   _ = (C ⊗ C) ◁ δ
         ∘ₗ δ ▷ C
         ∘ₗ δ := by simp [coassoc, LinearMap.lTensor_comp, LinearMap.comp_assoc]
   _ = (δ ⊗ₘ δ) ∘ₗ δ := by
    simp [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc]

private lemma gigaDiagram2 :
     (α C C (C ⊗ C)).symm.toLinearMap
     ∘ₗ C ◁ (α C C C).toLinearMap
     ∘ₗ (C ◁ ((β C C).toLinearMap ▷ C)
     ∘ₗ C ◁ (δ ▷ C))
     ∘ₗ C ◁ δ
     ∘ₗ δ
       = (α C C (C ⊗ C)).symm.toLinearMap
         ∘ₗ C ◁ (α C C C).toLinearMap
         ∘ₗ C ◁ (δ ▷ C)
         ∘ₗ C ◁ δ
         ∘ₗ δ := calc
   _ = (α C C (C ⊗ C)).symm.toLinearMap
     ∘ₗ C ◁ (α C C C).toLinearMap
     ∘ₗ C ◁ (((β C C).toLinearMap ∘ₗ δ) ▷ C)
     ∘ₗ C ◁ δ
     ∘ₗ δ := by simp only [LinearMap.lTensor_comp, LinearMap.rTensor_comp]
   _ = (α C C (C ⊗ C)).symm.toLinearMap
         ∘ₗ C ◁ (α C C C).toLinearMap
         ∘ₗ C ◁ (δ ▷ C)
         ∘ₗ C ◁ δ
         ∘ₗ δ := by simp [comul_comm]

private lemma gigaDiagram3 :
     (α C C (C ⊗ C)).symm.toLinearMap
     ∘ₗ C ◁ (α C C C).toLinearMap
     ∘ₗ C ◁ ((β C C).toLinearMap ▷ C)
     ∘ₗ (C ◁ (α C C C).symm.toLinearMap
     ∘ₗ ((α C C (C ⊗ C)).toLinearMap
     ∘ₗ (α C C (C ⊗ C)).symm.toLinearMap)
     ∘ₗ C ◁ (α C C C).toLinearMap)
     ∘ₗ C ◁ (δ ▷ C)
     ∘ₗ C ◁ δ
     ∘ₗ δ
       = (α C C (C ⊗ C)).symm.toLinearMap
         ∘ₗ C ◁ (α C C C).toLinearMap
         ∘ₗ (C ◁ ((β C C).toLinearMap ▷ C)
         ∘ₗ C ◁ (δ ▷ C))
         ∘ₗ C ◁ δ
         ∘ₗ δ := by
         simp
         rw [← LinearMap.lTensor_comp]
         simp [LinearMap.comp_assoc]

private lemma gigaDiagram4 :
     (α C C (C ⊗ C)).symm.toLinearMap
     ∘ₗ C ◁ (α C C C).toLinearMap
     ∘ₗ C ◁ ((β C C).toLinearMap ▷ C)
     ∘ₗ (C ◁ (α C C C).symm.toLinearMap
     ∘ₗ ((α C C (C ⊗ C)).toLinearMap
     ∘ₗ (α C C (C ⊗ C)).symm.toLinearMap)
     ∘ₗ C ◁ (α C C C).toLinearMap)
     ∘ₗ C ◁ (δ ▷ C)
     ∘ₗ C ◁ δ
     ∘ₗ δ
       = ((α _ _ _).symm.toLinearMap
         ∘ₗ (C ◁ (α _ _ _).toLinearMap
         ∘ₗ C ◁ ((β _ _).toLinearMap ▷ C)
         ∘ₗ C ◁ (α _ _ _).symm.toLinearMap)
         ∘ₗ (α _ _ _).toLinearMap)
         ∘ₗ (δ ⊗ₘ δ)
         ∘ₗ δ := by
          simp [LinearMap.comp_assoc]
          congr 3
          simp only [← LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
          rw [LinearMap.comp_assoc, coassoc]
          rw [← LinearMap.lTensor_comp_rTensor]
          simp only [← LinearMap.comp_assoc, LinearMap.lTensor_tensor2]
          simp [LinearMap.comp_assoc, coassoc]
          simp [← LinearMap.comp_assoc, LinearMap.lTensor_comp]

lemma gigaOmegaDiagram :
     (δ ⊗ₘ δ)
     ∘ₗ δ
       = (α _ _ _).symm.toLinearMap
         ∘ₗ C ◁ (α _ _ _).toLinearMap
         ∘ₗ C ◁ ((β _ _).toLinearMap ▷ C)
         ∘ₗ C ◁ (α _ _ _).symm.toLinearMap
         ∘ₗ (α _ _ _).toLinearMap
         ∘ₗ (δ ⊗ₘ δ)
         ∘ₗ δ := by
   nth_rewrite 1 [← gigaDiagram, ← gigaDiagram2, ← gigaDiagram3, gigaDiagram4]
   simp [LinearMap.comp_assoc]

/-- Comultiplication as a coalgebra hom. -/
def comulCoalgHom : C →ₗc[R] C ⊗[R] C where
  __ := δ
  counit_comp := calc
        μ ∘ₗ (ε ⊗ₘ ε) ∘ₗ δ
    _ = (μ ∘ₗ ε ▷ R) ∘ₗ (C ◁ ε ∘ₗ δ) := by
      rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ _ (.rTensor _ _)]; simp
    _ = ε := by ext; simp
  map_comp_comul := by
    rw [gigaOmegaDiagram]
    simp [LinearMap.comp_assoc]
    rw [tensorTensorTensorComm, leftComm]
    simp only [LinearEquiv.coe_trans]
    sorry

end Coalgebra

namespace HopfAlgebra
variable [CommSemiring C] [HopfAlgebra R C]

def antipodeCoalgHom : C →ₗc[R] C where
  __ := antipode (R := R) (A := C)
  counit_comp := sorry
  map_comp_comul := sorry

end HopfAlgebra
