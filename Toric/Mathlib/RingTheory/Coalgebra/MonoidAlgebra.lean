import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
import Toric.Mathlib.RingTheory.Coalgebra.Basic

open Coalgebra

namespace MonoidAlgebra
variable {R M : Type*} [CommRing R] [CommMonoid M]

instance : IsCocomm R <| MonoidAlgebra R M := sorry

end MonoidAlgebra

namespace AddMonoidAlgebra
variable {R M : Type*} [CommRing R] [AddCommMonoid M]

instance : IsCocomm R R[M] := sorry

end AddMonoidAlgebra
