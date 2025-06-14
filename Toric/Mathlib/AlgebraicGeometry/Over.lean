import Mathlib.AlgebraicGeometry.Over
import Toric.Mathlib.CategoryTheory.Comma.Over.OverClass

open CategoryTheory OverClass

namespace AlgebraicGeometry.Scheme.Hom
universe u
variable {S X Y Z : Scheme.{u}} [X.Over S] [Y.Over S] [Z.Over S]

@[simp] lemma asOver_id : Hom.asOver (𝟙 X) S = 𝟙 (X.asOver S) := rfl

@[simp] lemma asOver_comp (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver S] [g.IsOver S] :
    (f ≫ g).asOver S  = f.asOver S ≫ g.asOver S := rfl

@[simp] lemma asOver_inv (f : X ⟶ Y) [IsIso f] [f.IsOver S] :
    (inv f).asOver S  = inv (f.asOver S) := asOverHom_inv _

end AlgebraicGeometry.Scheme.Hom
