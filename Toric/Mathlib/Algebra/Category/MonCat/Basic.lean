import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.CategoryTheory.Yoneda

open CategoryTheory Opposite

def CommMonCat.coyoneda : CommMonCatᵒᵖ ⥤ CommMonCat ⥤ CommMonCat where
  obj M := { obj N := of (↑(unop M) →* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

def CommMonCat.coyonedaForget :
    coyoneda ⋙ (whiskeringRight _ _ _).obj (forget _) ≅ CategoryTheory.coyoneda :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ { hom f := ofHom f, inv f := f.hom })
    (fun _ ↦ rfl)) (fun _ ↦ rfl)

-- def CommMonCat.coyonedaRightForget :
--     coyonedaRight ⋙ (whiskeringRight _ _ _).obj (forget _) ≅
--       CategoryTheory.coyoneda ⋙ (whiskeringLeft _ _ _).obj (forget _) :=
  -- Iso.refl _
  -- NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ { hom f := f, inv f := f.hom })
  --   (fun _ ↦ rfl)) (fun _ ↦ rfl)
