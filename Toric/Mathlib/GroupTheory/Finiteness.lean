import Mathlib.GroupTheory.Finiteness
import Toric.Mathlib.Algebra.Group.Submonoid.Operations
import Toric.Mathlib.Data.Finset.Powerset

variable {M N : Type*} [Monoid M] [Monoid N] {P : Submonoid M} {Q : Submonoid N}

/-- The product of finitely generated submonoids is finitely generated. -/
@[to_additive "The product of finitely generated submonoids is finitely generated."]
lemma Submonoid.FG.prod (hP : P.FG) (hQ : Q.FG) : (P.prod Q).FG := by
  classical
  obtain ⟨bM, hbM⟩ := hP
  obtain ⟨bN, hbN⟩ := hQ
  refine ⟨bM ×ˢ singleton 1 ∪ singleton 1 ×ˢ bN, ?_⟩
  push_cast
  simp [Submonoid.closure_union, hbM, hbN]

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
  Monoid.FG.out.exists_minimal_closure_eq

namespace Prod
variable [Monoid N]

open Monoid in
/-- The product of finitely generated monoids is finitely generated. -/
@[to_additive "The product of finitely generated monoids is finitely generated."]
instance instMonoidFG [FG M] [FG N] : FG (M × N) where
  out := by rw [← Submonoid.top_prod_top]; exact .prod ‹FG M›.out ‹FG N›.out

end Prod
