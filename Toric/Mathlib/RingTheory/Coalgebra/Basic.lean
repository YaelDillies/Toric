import Mathlib.RingTheory.Coalgebra.Basic

open Coalgebra TensorProduct

universe u

variable {R C : Type*} [CommSemiring R]

namespace Coalgebra
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable (R C) in
/-- A coalgebra `C` is cocommutative if its comultiplication `δ : C → C ⊗ C` commutes with the
swapping `β : C ⊗ C ≃ C ⊗ C` of the factors in the tensor product.
-/
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

end Coalgebra
