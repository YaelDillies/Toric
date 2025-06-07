/-
Copyright (c) 2025 Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Luo
-/
import Toric.Mathlib.Algebra.AffineMonoid.Embedding
import Toric.GroupScheme.Torus
import Toric.ToricVariety.Defs

/-!
# Affine monoids give rise to toric varieties
-/

suppress_compilation

open Algebra AlgebraicGeometry Scheme CategoryTheory Limits AddMonoidAlgebra AddLocalization
  AffineAddMonoid

universe u
variable {R : CommRingCat.{u}} [IsDomain R] {M : Type u} [AddCancelCommMonoid M] [AddMonoid.FG M]
  [IsAddTorsionFree M]

namespace AffineToricVarietyFromMonoid

-- TODO: This used to be nicer when the torus was defined as `Spec _`
instance instMod_Class :
    Mod_Class (𝔾ₘ[Spec R, ULift <| Fin <| dim M].asOver (Spec R))
      ((Spec <| .of R[M]).asOver (Spec R)) where
  smul := Over.homMk sorry sorry
  -- (pullbackSpecIso _ _ _).hom ≫ (Spec.map <| CommRingCat.ofHom <| RingHom.comp
  -- (Algebra.TensorProduct.map (AddMonoidAlgebra.mapDomainAlgHom R _ <| embedding M)
  --   (.id _ _)).toRingHom (Bialgebra.comulAlgHom R _).toRingHom)
  one_smul := sorry
  mul_smul := sorry

noncomputable instance instToricVariety :
    ToricVariety (Spec R) (Diag (Spec R) (GrothendieckAddGroup M)) (Diag (Spec R) M) where
  __ := instMod_Class
  hom := Diag.map <| CommRingCat.ofHom <| algebraMap R R[M]
  torusEmb := sorry
    -- (splitTorusIsoSpecOver _ _).hom ≫ (Over.homMk
    -- (Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R <| embedding M))) <| by
    -- change Spec.map _ ≫ Spec.map _ = Spec.map _
    -- simp [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    -- congr! 2
    -- ext
    -- simp)
  isOpenImmersion_torusEmb := by
    stop
    obtain ⟨s, hsgen⟩ := AddMonoid.FG.fg_top (N := M)
    let x : AddMonoidAlgebra R M := ∏ z ∈ s, single z 1
    let alg : Algebra R[M] R[FreeAbelianGroup <| Fin <| dim M] :=
      (AddMonoidAlgebra.mapDomainAlgHom R _ <| embedding M).toAlgebra
    have _ : IsLocalization.Away x (AddMonoidAlgebra R <| FreeAbelianGroup <| Fin <| dim M) := by
      sorry
    exact .of_isLocalization x (M := R[FreeAbelianGroup <| Fin <| dim M])
  isDominant_torusEmb := by -- integral + open nonempty
    stop
    let img := RingHom.range (AddMonoidAlgebra.mapDomainRingHom R <| embedding M)
    have img_domain := Subring.instIsDomainSubtypeMem img
    have := (AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of (AddMonoidAlgebra R M)))
    sorry
  torusMul_comp_torusEmb := by
    stop
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    sorry

end AffineToricVarietyFromMonoid
#min_imports
