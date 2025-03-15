import Mathlib.Algebra.MonoidAlgebra.MapDomain

open Function

namespace MonoidAlgebra
variable {R M N : Type*} [Semiring R] {f : M → N}

lemma mapDomain_injective (hf : Injective f) : Injective (mapDomain (k := R) f) :=
  Finsupp.mapDomain_injective hf

end MonoidAlgebra

namespace AddMonoidAlgebra
variable {R M N : Type*} [Semiring R] {f : M → N}

lemma mapDomain_injective (hf : Injective f) : Injective (mapDomain (k := R) f) :=
  Finsupp.mapDomain_injective hf

end AddMonoidAlgebra
