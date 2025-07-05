import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Mathlib.Algebra.MonoidAlgebra.Defs
import Toric.Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct MonoidAlgebra Bialgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) [CommMonoid M]

lemma comulAlgHom_comp_mapRangeRingHom :
    (comulAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRangeRingHom f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRangeRingHom f) (mapRangeRingHom f)
        (by ext; simp) (by ext; simp))
        (comulAlgHom R (MonoidAlgebra R M)).toRingHom := by ext <;> simp

lemma counitAlgHom_comp_mapRangeRingHom :
    (counitAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRangeRingHom f) =
      f.comp (counitAlgHom R (MonoidAlgebra R M)).toRingHom := by
  ext <;> simp
