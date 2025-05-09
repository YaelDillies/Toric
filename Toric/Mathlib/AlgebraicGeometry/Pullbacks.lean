import Mathlib.AlgebraicGeometry.Pullbacks

suppress_compilation

open CategoryTheory

namespace AlgebraicGeometry
variable {S : Scheme}

instance : BraidedCategory (Over S) := .ofChosenFiniteProducts

end AlgebraicGeometry
