import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Over
import Toric.Mathlib.CategoryTheory.Comma.Over.OverClass

open CategoryTheory OverClass

namespace AlgebraicGeometry.Scheme
variable {X S : Scheme} [X.Over S] [IsAffine X]

noncomputable instance : (Spec Γ(X, ⊤)).Over S where
  hom := X.isoSpec.inv ≫ X ↘ S

instance : X.isoSpec.inv.IsOver S where
instance : X.isoSpec.hom.IsOver S where

end AlgebraicGeometry.Scheme
