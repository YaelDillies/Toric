import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.ChosenFiniteProducts.Over

open CategoryTheory

namespace AlgebraicGeometry
variable {S : Scheme}

noncomputable instance : ChosenFiniteProducts (Over S) := Over.chosenFiniteProducts _

end AlgebraicGeometry
