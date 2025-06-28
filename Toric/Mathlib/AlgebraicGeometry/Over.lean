import Toric.GroupScheme.HopfAffine
import Toric.Mathlib.AlgebraicGeometry.Pullbacks
import Toric.Mathlib.CategoryTheory.Comma.Over.OverClass

open CategoryTheory Limits OverClass MonoidalCategory Functor.LaxMonoidal
open TensorProduct

namespace AlgebraicGeometry.Scheme
variable {X S : Scheme} [X.Over S] [IsAffine X]

noncomputable instance : (Spec Γ(X, ⊤)).Over S where
  hom := X.isoSpec.inv ≫ X ↘ S

instance : X.isoSpec.inv.IsOver S where
instance : X.isoSpec.hom.IsOver S where

universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

instance [Algebra R S] [Bialgebra R T] :
    (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.IsOver Spec(S) where
  comp_over := by
    rw [← cancel_epi (pullbackSymmetry .. ≪≫ pullbackSpecIso' ..).inv,
      canonicallyOverPullback_over]
    simp [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullbackSpecIso']

variable (R S T) in
lemma μ_pullback_left_fst [Algebra R S] [Bialgebra R T] :
    («μ» (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))).left ≫
        pullback.fst _ _ =
    (((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver Spec(S) ⊗ₘ
        ((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver Spec(S))).left) ≫
          (pullbackSpecIso S (S ⊗[R] T) (S ⊗[R] T)).hom ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.mapRingHom (algebraMap _ _)
              Algebra.TensorProduct.includeRight.toRingHom
              Algebra.TensorProduct.includeRight.toRingHom
              (by simp [← IsScalarTower.algebraMap_eq])
              (by simp [← IsScalarTower.algebraMap_eq]))) ≫ (pullbackSpecIso R T T).inv := by
  simp
  ext <;> simp
  · simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom]
    simp [specOverSpec_over]
    erw [Over.tensorHom_left_fst_assoc]
    simp [pullbackSpecIso']
    rfl
  · simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Algebra.TensorProduct.mapRingHom_comp_includeRight]
    simp [specOverSpec_over]
    erw [Over.tensorHom_left_snd_assoc]
    simp [pullbackSpecIso']
    rfl

instance [Algebra R S] [Bialgebra R T] :
    IsMon_Hom <| (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver Spec(S) where
  one_hom := by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · simp [mon_ClassAsOverPullback_one, algSpec_ε_left (R := CommRingCat.of _),
      pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← Algebra.TensorProduct.algebraMap_def]
    · simp [mon_ClassAsOverPullback_one, algSpec_ε_left (R := CommRingCat.of _),
        pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← Algebra.TensorProduct.algebraMap_def,
        ← AlgHom.coe_restrictScalars R (Bialgebra.counitAlgHom S _), - AlgHom.coe_restrictScalars,
        ← AlgHom.comp_toRingHom, Bialgebra.counitAlgHom_comp_includeRight]
      rfl
  mul_hom := by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · simp [mon_ClassAsOverPullback_mul, pullbackSpecIso', specOverSpec_over, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, asOver, OverClass.asOver, AlgebraicGeometry.Scheme.mul_left,
        ← Algebra.TensorProduct.algebraMap_def, Hom.asOver, OverClass.asOverHom,
        pullback.condition]
      rfl
    · convert congr($(μ_pullback_left_fst R S T) ≫ (pullbackSpecIso R T T).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R T).toRingHom)) using 1
      · simp [mon_ClassAsOverPullback_mul, pullbackSpecIso', specOverSpec_over, OverClass.asOver,
          Hom.asOver, OverClass.asOverHom, mul_left]
      · simp [mon_ClassAsOverPullback_mul, pullbackSpecIso', specOverSpec_over, OverClass.asOver,
          Hom.asOver, OverClass.asOverHom, mul_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← Bialgebra.comul_includeRight]

end AlgebraicGeometry.Scheme
