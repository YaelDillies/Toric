import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

open CategoryTheory Limits

universe w w' u

namespace AlgebraicGeometry

instance Scheme.preservesLimits_Γ : PreservesLimitsOfSize.{w, w'} Scheme.Γ.{u} :=
  have := ΓSpec.adjunction.{u}.leftAdjoint_preservesColimits
  preservesLimitsOfSize_leftOp Scheme.Γ.rightOp

end AlgebraicGeometry
