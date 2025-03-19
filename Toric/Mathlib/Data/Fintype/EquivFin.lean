import Mathlib.Data.Fintype.EquivFin

-- TODO: Replace `Finset.exists_minimal`
theorem Finset.exists_minimal' {α : Type*} [Preorder α] (s : Finset α) (h : s.Nonempty) :
    ∃ m, Minimal (· ∈ s) m := by
  obtain ⟨c, hcs : c ∈ s⟩ := h
  have : WellFounded (@LT.lt { x // x ∈ s } _) := Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨⟨m, hms : m ∈ s⟩, -, H⟩ := this.has_min Set.univ ⟨⟨c, hcs⟩, trivial⟩
  refine ⟨m, hms, fun x hx ↦ ?_⟩
  simpa [not_lt_iff_not_le_or_ge, or_iff_not_imp_left] using H ⟨x, hx⟩ trivial

-- TODO: Replace `Finset.exists_maximal`
theorem Finset.exists_maximal' {α : Type*} [Preorder α] (s : Finset α) (h : s.Nonempty) :
    ∃ m, Maximal (· ∈ s) m :=
  @Finset.exists_minimal' αᵒᵈ _ s h
