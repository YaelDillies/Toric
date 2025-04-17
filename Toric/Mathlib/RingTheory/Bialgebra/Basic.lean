import Mathlib.RingTheory.Bialgebra.Basic

namespace Bialgebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Bialgebra R A]

lemma algebraMap_injective : Function.Injective (algebraMap R A) :=
  fun a b eq  ↦ by rw [← counit_algebraMap (A := A) a, ← counit_algebraMap (A := A) b, eq]

include R in
/--
A bialgebra over a nontrivial ring is nontrivial.
-/
lemma nontrivial [Nontrivial R] : Nontrivial A :=
  Set.nontrivial_of_nontrivial (s := (algebraMap R A) '' ⊤) ((Set.image_nontrivial
  (algebraMap_injective R A)).mpr Set.nontrivial_univ)

end Bialgebra
