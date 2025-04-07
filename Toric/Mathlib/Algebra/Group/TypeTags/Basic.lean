import Mathlib.Algebra.Group.TypeTags.Basic

namespace Additive
variable {α : Type*} {a b : Additive α}

@[ext] lemma ext (h : a.toMul = b.toMul) : a = b := h

end Additive

namespace Multiplicative
variable {α : Type*} {a b : Multiplicative α}

@[ext] lemma ext (h : a.toAdd = b.toAdd) : a = b := h

end Multiplicative
