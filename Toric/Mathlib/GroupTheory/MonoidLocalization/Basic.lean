import Mathlib.GroupTheory.MonoidLocalization.Basic

namespace Localization
variable {α : Type*} [CommMonoid α]

-- grab from https://github.com/leanprover-community/mathlib3/tree/alexjbest/grothendieck-group

@[to_additive]
instance : Inv (Localization (⊤ : Submonoid α)) where
  inv := rec (fun m s ↦ (.mk s ⟨m, Submonoid.mem_top m⟩ : Localization (⊤ : Submonoid α))) <| by
    intros m₁ m₂ s₁ s₂ h
    simpa [r_iff_exists, mk_eq_mk_iff, eq_comm, mul_comm] using h

@[to_additive (attr := simp)]
lemma mk_inv (m : α) (s : (⊤ : Submonoid α)) : (mk m s)⁻¹ = .mk s ⟨m, Submonoid.mem_top m⟩ := rfl

/-- The Grothendieck group is a group. -/
@[to_additive "The Grothendieck group is a group."]
instance : CommGroup (Localization (⊤ : Submonoid α)) where
  __ : CommMonoid (Localization (⊤ : Submonoid α)) := inferInstance
  inv_mul_cancel a := by
    induction' a using ind
    rw [mk_inv, mk_eq_monoidOf_mk', ←Submonoid.LocalizationMap.mk'_mul]
    convert Submonoid.LocalizationMap.mk'_self' _ _
    rw [mul_comm, Submonoid.coe_mul]

-- TODO yael: refactor AddLocalization.mk_zero_eq_addMonoidOf_mk 🤮

end Localization
