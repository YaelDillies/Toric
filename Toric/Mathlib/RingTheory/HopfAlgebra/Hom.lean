import Mathlib.RingTheory.Coalgebra.Hom
import Toric.Mathlib.RingTheory.HopfAlgebra.Basic

open Coalgebra TensorProduct

namespace HopfAlgebra
variable {R C : Type*} [CommSemiring R] [Semiring C] [HopfAlgebra R C] [IsCocomm R C]

/-- The antipode as a coalgebra hom. -/
def antipodeCoalgHom : C →ₗc[R] C where
  __ := antipode R (A := C)
  counit_comp := by ext a; exact counit_antipode _
  map_comp_comul := sorry

end HopfAlgebra
