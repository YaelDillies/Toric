import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.FiniteDimensional.Defs


namespace PointedCone

section Semiring

variable {R E : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E]
  [Module R E] (s : Set E)

local notation3 "R≥0" => {r : R // 0 ≤ r}

variable (R) in
abbrev span : PointedCone R E := Submodule.span R≥0 s

lemma subset_span : s ⊆ span R s := Submodule.subset_span

lemma span_union (s t : Set E) : span R (s ∪ t) = span R s ⊔ span R t :=
  Submodule.span_union s t

end Semiring 

end PointedCone
