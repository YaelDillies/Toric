import Mathlib.Algebra.FreeAbelianGroup.Finsupp

lemma Finsupp.toFreeAbelianGroup_single {σ : Type*} (x : σ) (n : ℕ) :
    Finsupp.toFreeAbelianGroup (X := σ) (.single x n) = n • .of x := by
  simp [Finsupp.toFreeAbelianGroup]
