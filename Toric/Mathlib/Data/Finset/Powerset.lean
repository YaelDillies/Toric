import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin

variable {ι : Type*}

lemma Finset.exists_minimal_subset {p : Finset ι → Prop} (s : Finset ι) (hs : p s) :
    ∃ t ⊆ s, Minimal (p ·) t := by
  classical
  obtain ⟨t, hts, ht, htmax⟩ : ∃ t ⊆ s, p t ∧ ∀ ⦃u : Finset ι⦄, u ⊆ s → u ⊆ t → p u → t ⊆ u := by
    simpa +contextual [and_assoc, forall_swap (α := p _), subset_trans,
      ssubset_iff_subset_not_subset]
      using {t ∈ s.powerset | p t}.exists_minimal <| by
        simpa [Finset.filter_nonempty_iff] using ⟨s, Subset.rfl, hs⟩
  exact ⟨t, hts, ht, fun u hu hut ↦ htmax (hut.trans hts) hut hu⟩
