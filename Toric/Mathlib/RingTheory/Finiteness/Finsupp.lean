import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RingTheory.Finiteness.Finsupp

namespace AddMonoidAlgebra
variable {ι R S : Type*} [Finite ι] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

instance moduleFinite : Module.Finite R S[ι] := .finsupp

end AddMonoidAlgebra

namespace MonoidAlgebra
variable {ι R S : Type*} [Finite ι] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

instance moduleFinite : Module.Finite R (MonoidAlgebra S ι) := .finsupp

end MonoidAlgebra
