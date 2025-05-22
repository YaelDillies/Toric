import Mathlib.Algebra.Group.TypeTags.Basic

variable {α : Type*}

@[ext] lemma Multiplicative.ext {a b : Multiplicative α} (hab : a.toAdd = b.toAdd) : a = b := hab
@[ext] lemma Additive.ext {a b : Additive α} (hab : a.toMul = b.toMul) : a = b := hab
