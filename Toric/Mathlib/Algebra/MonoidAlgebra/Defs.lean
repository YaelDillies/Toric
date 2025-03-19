import Mathlib.Algebra.MonoidAlgebra.Defs

--TODO(Paul-Lez): also add the Finsupp version
@[simp]
theorem AddMonoidAlgebra.single_ne_zero {k : Type*} [Semiring k] {G : Type*} {a : G} {b : k} :
    AddMonoidAlgebra.single a b ≠ 0 ↔ b ≠ 0 := by
  apply Iff.not AddMonoidAlgebra.single_eq_zero
