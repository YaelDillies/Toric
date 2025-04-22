/-
Copyright (c) 2025 Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Luo
-/
import Mathlib.RingTheory.Bialgebra.Basic
import Toric.AffineMonoid.Embedding
import Toric.ToricVariety.Defs

/-!
# Affine monoids give rise to toric varieties
-/

open AlgebraicGeometry Scheme CategoryTheory Limits AddMonoidAlgebra AddLocalization AffineMonoid

universe u
variable {R : CommRingCat.{u}} [IsDomain R] {S : Type u} [AddCancelCommMonoid S] [AddMonoid.FG S]
  [IsAddTorsionFree S]

variable (R S) in
noncomputable abbrev AffineToricVarietyFromMonoid : Over <| Spec R :=
  .mk <| Spec.map <| CommRingCat.ofHom <| algebraMap R R[S]

namespace AffineToricVarietyFromMonoid

instance instToricVariety :
    Mod_Class 𝔾ₘ[R, ULift <| Fin <| dim S] (.mk (Spec (.of R[S]) ↘ Spec R)) where

noncomputable instance instToricVariety :
    ToricVariety R (ULift <| Fin <| dim S) (Spec <| .of R[S]) where
  hom := Spec.map <| CommRingCat.ofHom <| algebraMap R R[S]
  smul := sorry
    -- (pullbackSpecIso _ _ _).hom ≫ (Spec.map <| CommRingCat.ofHom <| RingHom.comp
    -- (Algebra.TensorProduct.map (AddMonoidAlgebra.mapDomainAlgHom R _ <| embedding S)
    --   (.id _ _)).toRingHom (Bialgebra.comulAlgHom R _).toRingHom)
  torusEmb := sorry
    -- (splitTorusIsoSpecOver _ _).hom ≫ (Over.homMk
    -- (Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R <| embedding S))) <| by
    -- change Spec.map _ ≫ Spec.map _ = Spec.map _
    -- simp [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    -- congr! 2
    -- ext
    -- simp)
  isOpenImmersion_torusEmb := by
    stop
    obtain ⟨s, hsgen⟩ := AddMonoid.FG.fg_top (N := S)
    let x : AddMonoidAlgebra R S := ∏ z ∈ s, single z 1
    let alg : Algebra R[S] R[FreeAbelianGroup <| Fin <| dim S] :=
      (AddMonoidAlgebra.mapDomainAlgHom R _ <| embedding S).toAlgebra
    have _ : IsLocalization.Away x (AddMonoidAlgebra R <| FreeAbelianGroup <| Fin <| dim S) := by
      sorry
    exact .of_isLocalization x (S := R[FreeAbelianGroup <| Fin <| dim S])
  isDominant_torusEmb := by -- integral + open nonempty
    stop
    let img := RingHom.range (AddMonoidAlgebra.mapDomainRingHom R <| embedding S)
    have img_domain := Subring.instIsDomainSubtypeMem img
    have := (AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of (AddMonoidAlgebra R S)))
    sorry
  torusMul_comp_torusEmb := by
    stop
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    sorry

end AffineToricVarietyFromMonoid
