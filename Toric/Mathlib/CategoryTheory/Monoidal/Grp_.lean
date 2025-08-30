import Mathlib.CategoryTheory.Monoidal.Grp_

open CategoryTheory Mon_Class MonoidalCategory

/-! ### Tensor product of comm monoid/group objects -/

namespace Grp_Class.tensorObj
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {G H : C} [Grp_Class G] [Grp_Class H]

@[simps inv]
instance : Grp_Class (G ⊗ H) where
  inv := ι ⊗ₘ ι

end Grp_Class.tensorObj
