import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Functor

open CategoryTheory Mon_Class MonoidalCategory ChosenFiniteProducts

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Equivalence
variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts C]
variable {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts D]

-- FIXME: This is a hack. The following instance in mathlib isn't generalised to an arbitrary
-- lax-monoidal instance on the functor, so we're stuck using the one they use there:
-- https://github.com/leanprover-community/mathlib4/blob/bcaf02fadadb12180d9e38bc13b4036230c2f8c6/Mathlib/CategoryTheory/Monoidal/Grp_.lean#L331
attribute [local instance] Functor.monoidalOfChosenFiniteProducts

open Functor LaxMonoidal OplaxMonoidal

noncomputable def mapGrp (e : C ≌ D) [e.IsMonoidal] : Grp_ C ≌ Grp_ D where
  functor := e.functor.mapGrp
  inverse := e.inverse.mapGrp
  unitIso := by
    refine NatIso.ofComponents (fun X ↦ Grp_.mkIso (e.unitIso.app _) ?_ ?_) fun {X Y} f ↦ ?_
    · simp
    · simp [e.toAdjunction.map_μ_comp_counit_app_tensor_assoc]
      change _ = (e.unitIso.hom.app X.X ⊗ e.unitIso.hom.app X.X) ≫
        «μ» e.inverse (e.functor.obj X.X) (e.functor.obj X.X) ≫
          e.inverse.map («μ» e.functor X.X X.X) ≫ e.unitIso.inv.app (X.X ⊗ X.X) ≫ _
      sorry
    · ext
      simp
  counitIso := by
    refine NatIso.ofComponents (fun X ↦ Grp_.mkIso (e.counitIso.app _) ?_ ?_) fun {X Y} f ↦ ?_
    · simp
    · simp
      sorry
    · ext
      simp
  functor_unitIso_comp X := by ext; simp

end CategoryTheory.Equivalence
