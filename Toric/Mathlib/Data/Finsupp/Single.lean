import Mathlib.Data.Finsupp.Single

namespace Finsupp
variable {α M : Type*} [AddZeroClass M]

lemma single_add_apply (a : α) (b₁ b₂ : M) (j : α) :
    single a (b₁ + b₂) j = single a b₁ j + single a b₂ j := by simp

end Finsupp
