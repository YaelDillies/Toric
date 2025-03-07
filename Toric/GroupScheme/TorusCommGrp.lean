import Toric.GroupScheme.GroupScheme
import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.CommGrp_
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Yoneda
import Toric.Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib

open CategoryTheory AlgebraicGeometry Opposite Limits

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

class abbrev CommGrp_Class {C : Type*} [Category C] [ChosenFiniteProducts C] (X : C) :=
  Grp_Class X, IsCommMon X

instance {C : Type*} [Category C] [ChosenFiniteProducts C] (X : CommGrp_ C) :
    CommGrp_Class X.X where

noncomputable instance (σ : Type*) : Grp_Class (AlgebraicGeometry.TorusInt σ) :=
  Grp_Class.ofRepresentableBy _ (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget₂ _ Grp) (TorusInt.representableBy σ)

instance (σ : Type*) : IsCommMon (TorusInt σ) :=
  IsCommMon.ofRepresentableBy _ (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget₂ _ CommMonCat) (TorusInt.representableBy σ)

/-- If `X : C` is initial, then the under category of `X` is equivalent to `C`. -/
@[simps]
def CategoryTheory.Over.equivalenceOfIsTerminal
    {C : Type*} [Category C] {X : C} (hX : IsTerminal X) :
    Over X ≌ C where
  functor := Over.forget X
  inverse := { obj Y := Over.mk (hX.from Y), map f := Over.homMk f }
  unitIso := NatIso.ofComponents (fun Y ↦ Over.isoMk (Iso.refl _) (hX.hom_ext _ _))
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

instance {C : Type*} [Category C] [HasBinaryProducts C] {X : C} : (Over.star X).IsRightAdjoint  :=
  ⟨_, ⟨Over.forgetAdjStar X⟩⟩

noncomputable
def Over.forgetMapTerminal {C} [Category C] [HasTerminal C] (S : C)  :
    Over.forget _ ≅ Over.map (terminal.from S) ⋙
      (Over.equivalenceOfIsTerminal terminalIsTerminal).functor :=
  NatIso.ofComponents (fun X ↦ Iso.refl _) (by simp)

noncomputable section

def CommGrp_Torus (S : Scheme) (σ : Type*) : CommGrp_ (Over S) :=
  (Functor.mapCommGrp ((Over.equivalenceOfIsTerminal
    terminalIsTerminal).inverse ⋙ Over.pullback (terminal.from _))).obj
      (.mk' (AlgebraicGeometry.TorusInt σ))

/-- The (split) algebraic torus over `S` indexed by `σ`. -/
def Torus (S : Scheme) (σ : Type*) : Scheme := (CommGrp_Torus S σ).X.left

example (S : Scheme) (σ : Type*) : Torus S σ =
  pullback (terminal.from (TorusInt σ)) (terminal.from S) := rfl

instance (S : Scheme) (σ : Type*) : (Torus S σ).CanonicallyOver S where
  hom := (CommGrp_Torus S σ).X.hom

instance (S : Scheme) (σ : Type*) : CommGrp_Class (Over.mk (Torus S σ ↘ S)) :=
  inferInstanceAs (CommGrp_Class (CommGrp_Torus S σ).X)

def Torus.representableBy (S : Scheme) (σ : Type*) :
    ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget _).RepresentableBy
      (Over.mk (Torus S σ ↘ S)) :=
  ((((Over.mapPullbackAdj (terminal.from S)).comp
    (Over.equivalenceOfIsTerminal terminalIsTerminal).toAdjunction).comp <|
    (ΓSpec.adjunction.comp <| (CommRingCat.forget₂Adj CommRingCat.isInitial).op.comp <|
      CommGrp.forget₂CommMonAdj.op.comp <| AddCommGrp.equivalence.toAdjunction.op.comp <|
    (AddCommGrp.adj.op))).representableBy (op σ)).ofIso
    (isoWhiskerRight (NatIso.op (Over.forgetMapTerminal S))
      (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
        CommMonCat.units ⋙ forget _ ⋙ opOp _ ⋙ yoneda.obj (op σ)) ≪≫
        (isoWhiskerLeft ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
          CommMonCat.units ⋙ forget CommGrp) (opOpYoneda.app _)))
