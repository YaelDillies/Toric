import Mathlib.AlgebraicGeometry.Pullbacks
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Over

noncomputable section

open CategoryTheory CartesianMonoidalCategory Limits

namespace AlgebraicGeometry
universe u
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

open TensorProduct Algebra.TensorProduct CommRingCat RingHomClass

@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_fst' :
    (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom (algebraMap S _)) = pullback.fst _ _ := by
  simp [Algebra.TensorProduct.algebraMap_def]

@[reassoc]
lemma pullbackSpecIso_inv_fst' :
    (pullbackSpecIso R S T).inv ≫ pullback.fst _ _ = Spec.map (ofHom (algebraMap S _)) := by
  simp [← cancel_epi (pullbackSpecIso R S T).hom]

@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_base :
    (pullbackSpecIso R S T).hom ≫ Spec.map (ofHom (algebraMap R _)) =
      pullback.fst _ _ ≫ Spec.map (ofHom (algebraMap _ _)) := by
  simp [Algebra.TensorProduct.algebraMap_def]

namespace Scheme
variable {M S T : Scheme.{u}} [M.Over S] {f : T ⟶ S}

@[simps]
instance canonicallyOverPullback : (pullback (M ↘ S) f).CanonicallyOver T where
  hom := pullback.snd (M ↘ S) f

@[simps! -isSimp mul one]
instance monObjAsOverPullback [MonObj (asOver M S)] : MonObj (asOver (pullback (M ↘ S) f) T) := by
  unfold asOver OverClass.asOver at *; exact Over.monObjMkPullbackSnd

instance isCommMonObj_asOver_pullback [MonObj (asOver M S)] [IsCommMonObj (asOver M S)] :
    IsCommMonObj (asOver (pullback (M ↘ S) f) T) := by
  unfold asOver OverClass.asOver at *; exact Over.isCommMonObj_mk_pullbackSnd

instance GrpObjAsOverPullback [GrpObj (asOver M S)] : GrpObj (asOver (pullback (M ↘ S) f) T) := by
  unfold asOver OverClass.asOver at *; exact Over.grpObjMkPullbackSnd

instance : (pullback.fst (M ↘ S) (𝟙 S)).IsOver S := ⟨pullback.condition.trans (by simp)⟩

instance isMonHom_fst_id_right [MonObj (asOver M S)] :
    IsMonHom ((pullback.fst (M ↘ S) (𝟙 S)).asOver S) := by
  unfold asOver OverClass.asOver at *; exact Over.isMonHom_pullbackFst_id_right

end AlgebraicGeometry.Scheme
