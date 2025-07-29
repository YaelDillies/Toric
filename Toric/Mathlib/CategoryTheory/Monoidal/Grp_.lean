import Mathlib.CategoryTheory.Monoidal.Grp_

open CategoryTheory

namespace Grp_
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : Grp_ C}

@[simp] lemma forget₂Mon_obj_X (G : Grp_ C) : ((forget₂Mon_ C).obj G).X = G.X := rfl

end Grp_
