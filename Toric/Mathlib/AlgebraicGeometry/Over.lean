import Toric.GroupScheme.HopfAffine
import Toric.Mathlib.AlgebraicGeometry.Pullbacks
import Toric.Mathlib.CategoryTheory.Comma.Over.OverClass

open CategoryTheory Limits OverClass

namespace AlgebraicGeometry.Scheme
variable {X S : Scheme} [X.Over S] [IsAffine X]

noncomputable instance : (Spec Γ(X, ⊤)).Over S where
  hom := X.isoSpec.inv ≫ X ↘ S

instance : X.isoSpec.inv.IsOver S where
instance : X.isoSpec.hom.IsOver S where

universe u in
instance {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Bialgebra R T] :
    (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.IsOver Spec(S) where
  comp_over := by
    rw [← cancel_epi (pullbackSymmetry .. ≪≫ pullbackSpecIso' ..).inv,
      canonicallyOverPullback_over]
    simp [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullbackSpecIso']

end AlgebraicGeometry.Scheme
