import Mathlib.CategoryTheory.Comma.Over.OverClass

namespace CategoryTheory.OverClass
variable {C : Type*} [Category C] {X S : C} [OverClass X S]

@[simp] lemma asOverHom_id : asOverHom S (𝟙 X) = 𝟙 (asOver X S) := rfl

end CategoryTheory.OverClass
