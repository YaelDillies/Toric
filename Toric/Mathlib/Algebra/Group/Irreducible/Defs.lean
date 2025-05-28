import Mathlib.Algebra.Group.Irreducible.Defs

variable {M : Type*} [Monoid M] [Subsingleton Mˣ] {a b p : M}

@[to_additive]
lemma Irreducible.eq_one_or_eq_one (hp : Irreducible p) (hab : p = a * b) : a = 1 ∨ b = 1 := by
  simpa using hp.isUnit_or_isUnit hab
