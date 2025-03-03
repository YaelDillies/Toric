import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Monoidal.Yoneda

open CategoryTheory Opposite

def CategoryTheory.Adjunction.rightOp {C D : Type*} [Category C] [Category D]
    {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C} (a : F.rightOp ⊣ G) : G.rightOp ⊣ F where
  unit := NatTrans.unop a.counit
  counit := NatTrans.op a.unit
  left_triangle_components X := congr($(a.right_triangle_components (Opposite.op X)).op)
  right_triangle_components X := congr($(a.left_triangle_components (Opposite.unop X)).unop)

def CommMonCat.coyoneda : CommMonCatᵒᵖ ⥤ CommMonCat ⥤ CommMonCat where
  obj M := { obj N := of (↑(unop M) →* N), map f := ofHom (.compHom f.hom) }
  map f := { app N := ofHom (.compHom' f.unop.hom) }

def CommMonCat.coyonedaForget :
    coyoneda ⋙ (whiskeringRight _ _ _).obj (forget _) ≅ CategoryTheory.coyoneda :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ { hom f := ofHom f, inv f := f.hom })
    (fun _ ↦ rfl)) (fun _ ↦ rfl)

def CommGrp.coyonedaRight : Type _ᵒᵖ ⥤ CommGrp ⥤ CommGrp where
  obj M := { obj N := of (↑(unop M) → N),
             map f := ofHom (Pi.monoidHom fun i ↦ f.hom.comp (Pi.evalMonoidHom _ i)) }
  map f := { app N := ofHom (Pi.monoidHom fun i ↦ Pi.evalMonoidHom _ (f.unop i)) }

-- def CommMonCat.coyonedaRightForget :
--     coyonedaRight ⋙ (whiskeringRight _ _ _).obj (forget _) ≅
--       CategoryTheory.coyoneda ⋙ (whiskeringLeft _ _ _).obj (forget _) :=
  -- Iso.refl _
  -- NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ { hom f := f, inv f := f.hom })
  --   (fun _ ↦ rfl)) (fun _ ↦ rfl)

def opOpYoneda {C : Type*} [Category C] :
    yoneda ⋙ (whiskeringLeft _ _ _).obj (opOp C) ≅ coyoneda :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ (opEquiv (op Y) X).toIso)
    (fun _ ↦ rfl)) (fun _ ↦ rfl)

/-- The equivalence between `AddCommGrp` and `CommGrp`. -/
@[simps]
def AddCommGrp.equivalence : AddCommGrp ≌ CommGrp where
  functor := { obj X := .of (Multiplicative X), map f := CommGrp.ofHom f.hom.toMultiplicative }
  inverse := { obj X := .of (Additive X), map f := ofHom f.hom.toAdditive }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

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
  Mon_ClassOfRepresentableBy _ (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
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
  Mon_ClassOfRepresentableBy _ (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget₂ _ Grp ⋙ forget₂ _ _) (TorusInt.representableBy σ)

end

end AlgebraicGeometry
