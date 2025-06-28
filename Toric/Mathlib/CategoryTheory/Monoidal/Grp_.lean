import Mathlib.CategoryTheory.Monoidal.Grp_

open CategoryTheory

namespace Grp_
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : Grp_ C}

@[simp] lemma forget₂Mon_obj_X (G : Grp_ C) : ((forget₂Mon_ C).obj G).X = G.X := rfl

instance {f : G ⟶ H} [IsIso f] : IsIso f.hom := inferInstanceAs <| IsIso <| (forget C).map f

-- TODO: Replace `Grp_.mkIso`
/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
@[simps]
def mkIso' {G H : C} (f : G ≅ H) [Grp_Class G] [Grp_Class H] [IsMon_Hom f.hom] : mk G ≅ mk H where
  hom.hom := f.hom
  inv.hom := f.inv

end Grp_
