import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Toric.Mathlib.Algebra.MonoidAlgebra.Defs

namespace MonoidAlgebra
variable {M N R S : Type*} [CommSemiring R] [CommSemiring S] [Monoid M] [Monoid N]

lemma mapRangeRingHom_comp_mapDomainRingHom (f : R →+* S) (g : M →* N) :
    (mapRangeRingHom f).comp (mapDomainRingHom R g) =
      (mapDomainRingHom S g).comp (mapRangeRingHom f) := by aesop

end MonoidAlgebra
