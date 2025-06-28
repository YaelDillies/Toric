import Mathlib.RingTheory.FiniteType

open Polynomial

namespace Algebra.FiniteType
variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [FiniteType R S]

instance : FiniteType R S[X] := .trans ‹_› <| .polynomial ..

end Algebra.FiniteType
