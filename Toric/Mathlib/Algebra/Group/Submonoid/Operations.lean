import Mathlib.Algebra.Group.Submonoid.Operations

namespace Submonoid
variable {M N : Type*} [Monoid M] [Monoid N]

@[to_additive (attr := simp) closure_prod_zero]
lemma closure_prod_one (s : Set M) : closure (s ×ˢ ({1} : Set N)) = (closure s).prod ⊥ :=
  le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, .rfl⟩)
    (prod_le_iff.2 ⟨
      map_le_of_le_comap _ <| closure_le.2 fun _x hx => subset_closure ⟨hx, rfl⟩,
      by simp⟩)

@[to_additive (attr := simp) closure_zero_prod]
lemma closure_one_prod (t : Set N) : closure (({1} : Set M) ×ˢ t) = .prod ⊥ (closure t) :=
  le_antisymm
    (closure_le.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨.rfl, subset_closure⟩)
    (prod_le_iff.2 ⟨by simp,
      map_le_of_le_comap _ <| closure_le.2 fun _y hy => subset_closure ⟨rfl, hy⟩⟩)

end Submonoid
