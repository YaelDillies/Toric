import Mathlib.RingTheory.Bialgebra.Basic

namespace Bialgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A] [Nontrivial R]

variable (R A) in
include R A in
/-- A bialgebra over a nontrivial semiring is itself nontrivial. -/
lemma nontrivial : Nontrivial A where
  exists_pair_ne := ⟨0, 1, ne_of_apply_ne (Coalgebra.counit (R := R)) <| by simp⟩

end Bialgebra
