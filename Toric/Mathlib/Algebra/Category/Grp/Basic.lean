import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.CategoryTheory.Yoneda

open CategoryTheory Opposite

def CommGrp.coyoneda : CommGrpᵒᵖ ⥤ CommGrp ⥤ CommGrp where
  obj M := { obj N := of (↑(unop M) →* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

def CommGrp.coyonedaForget :
    coyoneda ⋙ (whiskeringRight _ _ _).obj (forget _) ≅ CategoryTheory.coyoneda :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ { hom f := ofHom f, inv f := f.hom })
    (fun _ ↦ rfl)) (fun _ ↦ rfl)

def CommGrp.coyonedaRight : Type _ᵒᵖ ⥤ CommGrp ⥤ CommGrp where
  obj M := { obj N := of (↑(unop M) → N),
             map f := ofHom (Pi.monoidHom fun i ↦ f.hom.comp (Pi.evalMonoidHom _ i)) }
  map f := { app N := ofHom (Pi.monoidHom fun i ↦ Pi.evalMonoidHom _ (f.unop i)) }
