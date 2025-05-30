import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
import Toric.Mathlib.RingTheory.Coalgebra.Basic

open Coalgebra

variable {R A M : Type*} [CommSemiring R] [Semiring A] [Module R A] [Coalgebra R A] [IsCocomm R A]

namespace MonoidAlgebra

instance instIsCocomm : IsCocomm R <| MonoidAlgebra A M := Finsupp.instIsCocomm

end MonoidAlgebra

namespace AddMonoidAlgebra

instance instIsCocomm : IsCocomm R A[M] := Finsupp.instIsCocomm

end AddMonoidAlgebra
