import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.Basic

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
local notation "δ" => comul
local infix:70 " ⊗ₘ " => TensorProduct.map

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
    have := congr((TensorProduct.assoc R _ C C).toLinearMap ∘ₗ
      ((TensorProduct.assoc R C C C).symm.toLinearMap ∘ₗ C ◁ $(comul_comm R C)) ▷ C ∘ₗ δ ▷ C ∘ₗ δ)
    simp [-comul_comm, LinearMap.comp_assoc] at this
    sorry

end Coalgebra

namespace HopfAlgebra
variable [CommSemiring C] [HopfAlgebra R C]

def antipodeCoalgHom : C →ₗc[R] C where
  __ := antipode (R := R) (A := C)
  counit_comp := sorry
  map_comp_comul := sorry

end HopfAlgebra
