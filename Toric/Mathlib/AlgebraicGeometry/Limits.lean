import Mathlib.AlgebraicGeometry.Limits

suppress_compilation

open CategoryTheory

namespace AlgebraicGeometry

instance : ChosenFiniteProducts Scheme := .ofFiniteProducts _
instance : BraidedCategory Scheme := .ofChosenFiniteProducts

end AlgebraicGeometry
