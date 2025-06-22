import Mathlib.CategoryTheory.Comma.Over.OverClass

namespace CategoryTheory
variable {C : Type*} [Category C] {X Y Z S : C} [OverClass X S] [OverClass Y S] [OverClass Z S]

variable (S) in
def Iso.asOver (e : X ≅ Y) [HomIsOver e.hom S] : OverClass.asOver X S ≅ OverClass.asOver Y S :=
  Over.isoMk e (by simp)

@[simp] lemma Iso.asOver_hom (e : X ≅ Y) [HomIsOver e.hom S] :
    (e.asOver S).hom = OverClass.asOverHom S e.hom := rfl

@[simp] lemma Iso.asOver_inv (e : X ≅ Y) [HomIsOver e.hom S] :
    have : HomIsOver e.inv S := ⟨by rw [e.inv_comp_eq]; simp⟩
    (e.asOver S).inv = OverClass.asOverHom S e.inv := rfl

namespace OverClass

instance (f : X ⟶ Y) [IsIso f] [HomIsOver f S] : IsIso (asOverHom S f) :=
  have : IsIso ((Over.forget S).map (asOverHom S f)) := ‹_›
  isIso_of_reflects_iso _ (Over.forget _)

attribute [local simp] Iso.inv_comp_eq in
instance {e : X ≅ Y} [HomIsOver e.hom S] : HomIsOver e.inv S where

attribute [local simp ←] Iso.eq_inv_comp in
instance {e : X ≅ Y} [HomIsOver e.inv S] : HomIsOver e.hom S where

instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).hom S := ‹_›
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).inv S where
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (inv f) S where

@[simp] lemma asOverHom_id : asOverHom S (𝟙 X) = 𝟙 (asOver X S) := rfl

@[simp] lemma asOverHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S] :
    asOverHom S (f ≫ g) = asOverHom S f ≫ asOverHom S g := rfl

@[simp] lemma asOverHom_inv (f : X ⟶ Y) [IsIso f] [HomIsOver f S] :
    asOverHom S (inv f) = inv (asOverHom S f) := by simp [← hom_comp_eq_id, ← asOverHom_comp]

end CategoryTheory.OverClass
