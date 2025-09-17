import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_

/-! ### Pushforward of a group object -/

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D] {G : C} [GrpObj G] (F : C ⥤ D) [F.Monoidal]

open scoped Obj

/-- The image of a group object under a monoidal functor is a group object. -/
noncomputable abbrev grpObjObj : GrpObj (F.obj G) := (F.mapGrp.obj ⟨G⟩).grp

scoped[Obj] attribute [instance] CategoryTheory.Functor.grpObjObj

end CategoryTheory.Functor

/-! ### `mapGrp` is braided -/

namespace CategoryTheory.Functor
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal]

open LaxMonoidal Monoidal

variable [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.Braided]

noncomputable instance mapGrp.instMonoidal : F.mapGrp.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
  { εIso := (Grp_.fullyFaithfulForget₂Mon _).preimageIso (εIso F.mapMon)
    μIso X Y := (Grp_.fullyFaithfulForget₂Mon _).preimageIso (μIso F.mapMon X.toMon Y.toMon)
    μIso_hom_natural_left f Z := by convert μ_natural_left F.mapMon f Z.toMon using 1
    μIso_hom_natural_right Z f := by convert μ_natural_right F.mapMon Z.toMon f using 1
    associativity X Y Z := by convert associativity F.mapMon X.toMon Y.toMon Z.toMon using 1
    left_unitality X := by convert left_unitality F.mapMon X.toMon using 1
    right_unitality X := by convert right_unitality F.mapMon X.toMon using 1 }

noncomputable instance mapGrp.instBraided : F.mapGrp.Braided where
  braided X Y := by convert Braided.braided (F := F.mapMon) X.toMon Y.toMon using 1

end CategoryTheory.Functor
