import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Finset
variable {ι M : Type*} [CommMonoid M] [Subsingleton Mˣ] {s : Finset ι} {f : ι → M}

-- TODO: Replace `Finset.prod_eq_one_iff'`/`Finset.sum_eq_zero_iff`
@[to_additive (attr := simp)] lemma prod_eq_one_iff'' : ∏ i ∈ s, f i = 1 ↔ ∀ i ∈ s, f i = 1 := by
  induction' s using Finset.cons_induction with i s hi ih <;> simp [*]

end Finset
