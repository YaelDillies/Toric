import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Mathlib.Algebra.MonoidAlgebra.Defs
import Toric.Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct MonoidAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) [CommMonoid M]

lemma comulAlgHom_comp_mapRangeRingHom :
    (Bialgebra.comulAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRangeRingHom f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRangeRingHom f) (mapRangeRingHom f)
        (by classical ext; simp [single_apply, apply_ite f])
        (by classical ext; simp [single_apply, apply_ite f]))
        (Bialgebra.comulAlgHom R (MonoidAlgebra R M)).toRingHom := by ext <;> simp

lemma counitAlgHom_comp_mapRangeRingHom :
    (Bialgebra.counitAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRangeRingHom f) =
      f.comp (Bialgebra.counitAlgHom R (MonoidAlgebra R M)).toRingHom := by
  ext <;> simp
