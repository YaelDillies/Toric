import Mathlib.GroupTheory.Finiteness
import Toric.Mathlib.Data.Finset.Powerset

variable {M N : Type*} [Monoid M] [Monoid N] {P : Submonoid M} {Q : Submonoid N}

/-- A finitely generated submonoid has a minimal generating set. -/
@[to_additive "A finitely generated submonoid has a minimal generating set."]
lemma Submonoid.FG.exists_minimal_closure_eq (hP : P.FG) :
    ∃ S : Finset M, Minimal (closure ·.toSet = P) S := by
  classical
  obtain ⟨S₀, hS₀⟩ := hP
  obtain ⟨S, -, hS⟩ := S₀.exists_minimal_subset (p := (closure · = P)) hS₀
  exact ⟨S, hS⟩

variable (M) in
/-- A finitely generated monoid has a minimal generating set. -/
@[to_additive "A finitely generated monoid has a minimal generating set."]
lemma Submonoid.exists_minimal_closure_eq_top [Monoid.FG M] :
    ∃ S : Finset M, Minimal (Submonoid.closure ·.toSet = ⊤) S :=
  Monoid.FG.fg_top.exists_minimal_closure_eq
