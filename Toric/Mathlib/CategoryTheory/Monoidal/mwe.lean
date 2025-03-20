import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Grp_

open CategoryTheory Mon_Class MonoidalCategory ChosenFiniteProducts

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Equivalence
variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts C]
variable {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts D]

noncomputable def mapGrp (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal]
    [e.IsMonoidal] :
    Grp_ C ≌ Grp_ D where
  functor := e.functor.mapGrp
  inverse := e.inverse.mapGrp
  unitIso := by
    refine NatIso.ofComponents (fun X ↦ Grp_.mkIso (e.unitIso.app _) ?_ ?_) fun {X Y} f ↦ ?_
    · dsimp
      simp
      have := NatTrans.IsMonoidal.unit (τ := e.unit)
      change X.one ≫ e.unit.app X.X = _
      sorry
    · simp
      sorry
    · ext
      simp
  counitIso := by
    refine NatIso.ofComponents (fun X ↦ Grp_.mkIso (e.counitIso.app _) ?_ ?_) fun {X Y} f ↦ ?_
    · simp
      sorry
    · simp
      sorry
    · ext
      simp
  functor_unitIso_comp X := by ext; simp

end CategoryTheory.Equivalence
