import Mathlib.CategoryTheory.Comma.Over.Basic

namespace CategoryTheory.Over
universe v
variable {C : Type*} [Category.{v} C] {X : C} {U V : Over X} {f : U.left ⟶ V.left}

instance epi_homMk [Epi f] (w) : Epi (homMk f w) := (forget X).epi_of_epi_map ‹_›

end CategoryTheory.Over
