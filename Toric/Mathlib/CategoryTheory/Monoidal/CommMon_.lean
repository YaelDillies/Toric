import Mathlib.CategoryTheory.Monoidal.CommMon_

open CategoryTheory Mon_Class MonoidalCategory

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] {M : C} [Mon_Class M] [IsCommMon M]
  (F : C ⥤ D) [F.LaxBraided]

scoped[Obj] attribute [instance] CategoryTheory.Functor.obj.instMon_Class

open scoped Obj

instance isCommMonObj : IsCommMon (F.obj M) := (F.mapCommMon.obj (.mk M)).comm

end CategoryTheory.Functor
