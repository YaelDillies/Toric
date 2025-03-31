import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Monoidal.Yoneda
import Toric.Mathlib.Algebra.Category.Grp.Basic
import Toric.Mathlib.Algebra.Category.MonCat.Basic
import Toric.Mathlib.CategoryTheory.Yoneda

open CategoryTheory Opposite

namespace AlgebraicGeometry

noncomputable section

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

def DiagInt (G : Type*) [CommMonoid G] : Scheme := Spec (.of (MonoidAlgebra (ULift ℤ) G))

def DiagInt.representableBy (G : Type*) [CommMonoid G] :
    (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
      CommMonCat.coyoneda.obj (op (.of G)) ⋙ forget _).RepresentableBy
      (DiagInt G) :=
  letI e : opOp CommMonCat ⋙ yoneda.obj (op (.of G)) ≅ CommMonCat.coyoneda.obj _ ⋙ forget _ :=
    opOpYoneda.app (op _) ≪≫ CommMonCat.coyonedaForget.symm.app (op (.of G))
  letI e' := isoWhiskerLeft (Scheme.Γ ⋙ forget₂ _ CommMonCat) e
  ((ΓSpec.adjunction.comp (CommRingCat.forget₂Adj CommRingCat.isInitial).op).representableBy
    (op (.of G))).ofIso e'

instance (G : Type*) [CommMonoid G] : Mon_Class (DiagInt G) :=
  Mon_Class.ofRepresentableBy _ (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
    CommMonCat.coyoneda.obj (op (.of G)) ⋙ forget₂ _ _) (DiagInt.representableBy G)

def TorusInt (σ : Type*) : Scheme := DiagInt (Multiplicative (FreeAbelianGroup σ))

def TorusInt.representableBy (σ : Type*) :
    (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget _).RepresentableBy
      (TorusInt σ) :=
  ((ΓSpec.adjunction.comp <| (CommRingCat.forget₂Adj CommRingCat.isInitial).op.comp <|
    CommGrp.forget₂CommMonAdj.op.comp <| AddCommGrp.equivalence.toAdjunction.op.comp <|
    (AddCommGrp.adj.op)).representableBy (op σ)).ofIso
    (isoWhiskerLeft (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙ forget CommGrp)
      (opOpYoneda.app _))

instance (σ : Type*) : Mon_Class (TorusInt σ) :=
  Mon_Class.ofRepresentableBy _ (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget₂ _ Grp ⋙ forget₂ _ _) (TorusInt.representableBy σ)

end

end AlgebraicGeometry
