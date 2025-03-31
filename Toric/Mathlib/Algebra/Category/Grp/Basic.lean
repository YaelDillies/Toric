import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Pi.Lemmas

open CategoryTheory Opposite

def CommGrp.coyonedaRight : Type _ᵒᵖ ⥤ CommGrp ⥤ CommGrp where
  obj M := { obj N := of (↑(unop M) → N),
             map f := ofHom (Pi.monoidHom fun i ↦ f.hom.comp (Pi.evalMonoidHom _ i)) }
  map f := { app N := ofHom (Pi.monoidHom fun i ↦ Pi.evalMonoidHom _ (f.unop i)) }

/-- The equivalence between `AddCommGrp` and `CommGrp`. -/
@[simps]
def AddCommGrp.equivalence : AddCommGrp ≌ CommGrp where
  functor := { obj X := .of (Multiplicative X), map f := CommGrp.ofHom f.hom.toMultiplicative }
  inverse := { obj X := .of (Additive X), map f := ofHom f.hom.toAdditive }
  unitIso := .refl _
  counitIso := .refl _
