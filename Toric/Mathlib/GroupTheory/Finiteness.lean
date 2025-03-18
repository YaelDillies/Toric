import Mathlib.GroupTheory.Finiteness
import Toric.Mathlib.Algebra.Group.Submonoid.Operations

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

namespace Prod
variable [Monoid N]

open Monoid in
/-- The product of finitely generated monoids is finitely generated. -/
@[to_additive "The product of finitely generated monoids is finitely generated."]
instance instMonoidFG [FG M] [FG N] : FG (M × N) where
  out := by rw [← Submonoid.top_prod_top]; exact .prod ‹FG M›.out ‹FG N›.out

end Prod
