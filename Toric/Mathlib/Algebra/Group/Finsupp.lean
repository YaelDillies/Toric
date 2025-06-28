import Mathlib.Algebra.Group.Finsupp

@[simp]
lemma AddEquiv.finsuppUnique_apply {M ι : Type*} [AddZeroClass M] [Unique ι] (v : ι →₀ M) :
    AddEquiv.finsuppUnique v = v default := rfl
