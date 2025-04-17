import Mathlib.RingTheory.Bialgebra.Basic

universe u v

namespace Bialgebra

variable (R : Type u) (A : Type v)
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Nontrivial R]

lemma nontrivial : Nontrivial A where
  exists_pair_ne := by
    refine ⟨0, 1, fun eq ↦ ?_⟩
    apply_fun Coalgebra.counit (R := R) (A := A) at eq
    simp only [map_zero, counit_one, zero_ne_one] at eq

end Bialgebra
