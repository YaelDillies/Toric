import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section

open CategoryTheory CartesianMonoidalCategory Limits

namespace AlgebraicGeometry.Scheme
universe u
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_base (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    (pullbackSpecIso R S T).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) =
      pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _)) := by
  simp [Algebra.TensorProduct.algebraMap_def]

@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_fst' (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    (pullbackSpecIso R S T).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S _)) =
      pullback.fst _ _ := by
  simp [Algebra.TensorProduct.algebraMap_def]

@[reassoc]
lemma pullbackSpecIso_inv_fst' (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    (pullbackSpecIso R S T).inv ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (algebraMap S _)) := by
  simp [← cancel_epi (pullbackSpecIso R S T).hom]

end AlgebraicGeometry.Scheme
