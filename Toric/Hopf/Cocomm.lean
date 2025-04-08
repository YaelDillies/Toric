import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.Basic

open Coalgebra TensorProduct

universe u

variable {R C : Type u} [CommSemiring R]

section Coalgebra
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable (R C) in
class IsCocomm where
  comul_comm' : (TensorProduct.comm R C C).comp (comul (R := R)) = comul (R := R) (A := C)

namespace IsCocomm

variable (R C) in
@[simp]
theorem comul_comm [IsCocomm R C] :
    (TensorProduct.comm R C C).comp (comul (R := R)) = comul (R := R) (A := C) := comul_comm'

end IsCocomm

variable (R) in
instance : IsCocomm R R where comul_comm' := by ext; simp

variable [IsCocomm R C]

local notation "ε" => counit (R := R) (A := C)
local notation "μ" => LinearMap.mul' R R
local notation "δ" => comul
local infix:70 " ⊗ₘ " => TensorProduct.map

def comulCoalgHom : C →ₗc[R] C ⊗[R] C :=
  .mk δ
  (calc
        (μ ∘ₗ (ε ⊗ₘ ε)) ∘ₗ δ
  _ = (μ ∘ₗ (ε ⊗ₘ LinearMap.id) ∘ₗ (LinearMap.id ⊗ₘ ε)) ∘ₗ δ := by simp [← TensorProduct.map_comp]
  _ = μ ∘ₗ (ε ⊗ₘ LinearMap.id) ∘ₗ (LinearMap.id ⊗ₘ ε) ∘ₗ δ := by simp [LinearMap.comp_assoc]
  _ = _ := by ext; simp [← LinearMap.lTensor_def])
  (by dsimp; sorry)

end Coalgebra

namespace HopfAlgebra
variable [CommSemiring C] [HopfAlgebra R C]

def antipodeCoalgHom : C →ₗc[R] C :=
  .mk (antipode (R := R) (A := C))
  sorry
  sorry

end HopfAlgebra
