import Mathlib.Geometry.Convex.Cone.Dual
import Toric.Mathlib.Geometry.Convex.Cone.Pointed

namespace PointedCone
variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

-- TODO: Replace `dual_span`
@[simp] lemma dual_span' (s : Set M) : dual p (span R s) = dual p s := dual_span ..

end PointedCone
