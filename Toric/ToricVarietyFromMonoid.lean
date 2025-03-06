import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.MonoidAlgebra.Defs
import Toric.AffineMonoid
import Toric.ToricVariety
import Mathlib.AlgebraicGeometry.Properties

open AlgebraicGeometry CategoryTheory Limits AddMonoidAlgebra AddLocalization

noncomputable abbrev AddMonoidMapLift (R) {M N} [CommRing R] [AddMonoid M] [AddMonoid N] :
    (f : M →+ N) → AddMonoidAlgebra R M →ₐ[R] AddMonoidAlgebra R N :=
  fun f ↦ AddMonoidAlgebra.lift R M (AddMonoidAlgebra R N)
            (.comp AddMonoidAlgebra.singleHom <| .prod 1 f.toMultiplicative)
@[to_additive existing]
noncomputable abbrev MonoidMapLift (R) {M N} [CommRing R] [Monoid M] [Monoid N] :
    (f : M →* N) → MonoidAlgebra R M →ₐ[R] MonoidAlgebra R N :=
  fun f ↦ MonoidAlgebra.lift R M (MonoidAlgebra R N) (.comp MonoidAlgebra.singleHom <| .prod 1 f)

-- TODO to_additive etc
lemma AddMonoidMapLiftInj (R) {M N} [CommRing R] [AddMonoid M] [AddMonoid N] (f : M →+ N) :
    Function.Injective f → Function.Injective (AddMonoidMapLift R f) := sorry

variable {R : CommRingCat}
variable {S} [AddCommMonoid S] [hFG : AddMonoid.FG S] [IsCancelAdd S] [hTF : IsAddFree S]

variable (R S) in
noncomputable abbrev AffineToricVarietyFromMonoid := Spec <| CommRingCat.of <| AddMonoidAlgebra R S

noncomputable instance : (AffineToricVarietyFromMonoid R S).Over (Spec R) where
  hom := Spec.map <| CommRingCat.ofHom <| algebraMap R _

noncomputable instance : ToricVariety R (dim S) (AffineToricVarietyFromMonoid R S) where
  torusEmb := Spec.map <| CommRingCat.ofHom (AddMonoidMapLift R <| AffineLatticeHom S).toRingHom
  torusEmb_comp_overHom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  isOpenImmersion_torusEmb := by
    obtain ⟨s, hsgen, hsfin⟩ := AddMonoid.fg_iff.mp hFG
    let x := ∏ z ∈ Set.Finite.toFinset hsfin, (single z 1 : AddMonoidAlgebra R S)
    let alg : Algebra R[S] R[FreeAbelianGroup <| Fin <| dim S] :=
      (AddMonoidMapLift R (AffineLatticeHom S)).toAlgebra
    have _ : IsLocalization.Away x (AddMonoidAlgebra R <| FreeAbelianGroup <| Fin <| dim S) := by
      sorry
    exact IsOpenImmersion.of_isLocalization x (S := R[FreeAbelianGroup <| Fin <| dim S])
  isDominant_torusEmb := by -- integral + open nonempty
    let img := RingHom.range (AddMonoidMapLift R <| AffineLatticeHom S).toRingHom
    have img_domain := Subring.instIsDomainSubtypeMem img
    have := (AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of (AddMonoidAlgebra R S)))
    sorry
  torusAct := (pullbackSpecIso _ _ _).hom ≫ (Spec.map <| CommRingCat.ofHom <| RingHom.comp
    (Algebra.TensorProduct.map (AddMonoidMapLift R <| AffineLatticeHom S) (AlgHom.id _ _)).toRingHom
    (Bialgebra.comulAlgHom R _).toRingHom)
  torusMul_comp_torusEmb := by
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    sorry
