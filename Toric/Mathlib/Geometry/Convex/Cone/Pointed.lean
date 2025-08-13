import Mathlib.Geometry.Convex.Cone.Pointed

namespace PointedCone
variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E]
  [Module 𝕜 E] {S : Set E}

variable (𝕜 S) in
/-- The span of a set `S` is the smallest pointed cone that contains `S`.

Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
submodule span of `S` w.r.t. nonnegative scalars. -/
abbrev span : PointedCone 𝕜 E := Submodule.span _ S

lemma subset_span : S ⊆ PointedCone.span 𝕜 S := Submodule.subset_span

end PointedCone
