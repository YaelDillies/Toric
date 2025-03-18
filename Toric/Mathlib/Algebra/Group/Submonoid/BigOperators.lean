import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators

namespace Submonoid
variable {M : Type*} [CommMonoid M] {s : Finset M} {x : M}

@[to_additive]
lemma mem_closure_finset : x ∈ closure s ↔ ∃ n : M → ℕ, x = ∏ a ∈ s, a ^ n a where
  mp hx := by
    classical
    induction' hx using closure_induction with x hx x y _ _ hx hy
    · simp only [Finset.mem_coe] at hx
      exact ⟨Pi.single x 1, by simp [hx, Pi.single_apply]⟩
    · exact ⟨0, by simp⟩
    · obtain ⟨m, rfl⟩ := hx
      obtain ⟨n, rfl⟩ := hy
      exact ⟨m + n, by simp [pow_add, Finset.prod_mul_distrib]⟩
  mpr := by rintro ⟨n, rfl⟩; exact prod_mem _ fun x hx ↦ pow_mem (subset_closure hx) _

end Submonoid
