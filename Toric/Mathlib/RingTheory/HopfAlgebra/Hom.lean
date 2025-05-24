
import Toric.Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.Algebra.Module.Equiv.Defs
import Toric.Mathlib.LinearAlgebra.TensorProduct.Associator
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic

open Coalgebra TensorProduct

namespace HopfAlgebra
variable {R C : Type*} [CommSemiring R] [Semiring C] [HopfAlgebra R C] [IsCocomm R C]

def antipodeCoalgHom : C →ₗc[R] C where
  __ := antipode (R := R) (A := C)
  counit_comp := sorry
  map_comp_comul := sorry

end HopfAlgebra
