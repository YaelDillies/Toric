/-
Copyright (c) 2025 Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Luo
-/
import Mathlib.AlgebraicGeometry.Properties
import Toric.AffineMonoid.Embedding
import Toric.ToricVariety

/-!
# Affine monoids give rise to toric varieties
-/

open AlgebraicGeometry CategoryTheory Limits AddMonoidAlgebra AddLocalization AffineMonoid

variable {R : CommRingCat} [IsDomain R] {S : Type*} [AddCancelCommMonoid S] [AddMonoid.FG S]
  [IsAddTorsionFree S]

variable (R S) in
noncomputable abbrev AffineToricVarietyFromMonoid := Spec <| CommRingCat.of <| AddMonoidAlgebra R S

noncomputable instance : (AffineToricVarietyFromMonoid R S).Over (Spec R) where
  hom := Spec.map <| CommRingCat.ofHom <| algebraMap R _

noncomputable instance : ToricVariety R (dim S) (AffineToricVarietyFromMonoid R S) where
  torusEmb :=
    Spec.map <| CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R <| embedding S)
  torusEmb_comp_overHom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr! 2
    ext
    simp
  isOpenImmersion_torusEmb := by
    obtain ⟨s, hsgen⟩ := AddMonoid.FG.out (N := S)
    let x : AddMonoidAlgebra R S := ∏ z ∈ s, single z 1
    let alg : Algebra R[S] R[FreeAbelianGroup <| Fin <| dim S] :=
      (AddMonoidAlgebra.mapDomainAlgHom R _ <| embedding S).toAlgebra
    have _ : IsLocalization.Away x (AddMonoidAlgebra R <| FreeAbelianGroup <| Fin <| dim S) := by
      sorry
    exact .of_isLocalization x (S := R[FreeAbelianGroup <| Fin <| dim S])
  isDominant_torusEmb := by -- integral + open nonempty
    let img := RingHom.range (AddMonoidAlgebra.mapDomainRingHom R <| embedding S)
    have img_domain := Subring.instIsDomainSubtypeMem img
    have := (AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of (AddMonoidAlgebra R S)))
    sorry
  torusAct := (pullbackSpecIso _ _ _).hom ≫ (Spec.map <| CommRingCat.ofHom <| RingHom.comp
    (Algebra.TensorProduct.map (AddMonoidAlgebra.mapDomainAlgHom R _ <| embedding S)
      (.id _ _)).toRingHom (Bialgebra.comulAlgHom R _).toRingHom)
  torusMul_comp_torusEmb := by
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    sorry
