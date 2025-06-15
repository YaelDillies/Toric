import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Toric.Mathlib.Algebra.MonoidAlgebra.Defs

variable {M N O R S : Type*} [CommSemiring R] [CommSemiring S]

namespace MonoidAlgebra
variable [Monoid M] [Monoid N] [Monoid O]

@[simp] lemma mapDomainRingHom_id :
    mapDomainRingHom R (MonoidHom.id M) = .id (MonoidAlgebra R M) := by ext <;> simp

@[simp] lemma mapDomainRingHom_comp (f : N →* O) (g : M →* N) :
    mapDomainRingHom R (f.comp g) = (mapDomainRingHom R f).comp (mapDomainRingHom R g) := by
  ext <;> simp

lemma mapRangeRingHom_comp_mapDomainRingHom (f : R →+* S) (g : M →* N) :
    (mapRangeRingHom f).comp (mapDomainRingHom R g) =
      (mapDomainRingHom S g).comp (mapRangeRingHom f) := by aesop

end MonoidAlgebra

namespace AddMonoidAlgebra
variable [AddMonoid M] [AddMonoid N] [AddMonoid O]

@[simp] lemma mapDomainRingHom_id : mapDomainRingHom R (AddMonoidHom.id M) = .id R[M] := by
  ext <;> simp

@[simp] lemma mapDomainRingHom_comp (f : N →+ O) (g : M →+ N) :
    mapDomainRingHom R (f.comp g) = (mapDomainRingHom R f).comp (mapDomainRingHom R g) := by
  ext <;> simp

end AddMonoidAlgebra
