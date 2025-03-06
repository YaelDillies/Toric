import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.MonoidAlgebra.Defs
import Toric.AffineMonoid
import Toric.ToricVariety

open AlgebraicGeometry CategoryTheory Limits

noncomputable abbrev AddMonoidMapLift {R M N} [CommRing R] [AddMonoid M] [AddMonoid N] :
    (f : M →+ N) → AddMonoidAlgebra R M →ₐ[R] AddMonoidAlgebra R N :=
  fun f ↦ AddMonoidAlgebra.lift R M (AddMonoidAlgebra R N)
            (.comp AddMonoidAlgebra.singleHom <| .prod 1 f.toMultiplicative)
@[to_additive existing]
noncomputable abbrev MonoidMapLift {R M N} [CommRing R] [Monoid M] [Monoid N] (f : M →* N) :
    MonoidAlgebra R M →ₐ[R] MonoidAlgebra R N :=
  MonoidAlgebra.lift R M (MonoidAlgebra R N) (.comp MonoidAlgebra.singleHom <| .prod 1 f)

variable {R : CommRingCat} {S} [AddCommMonoid S] [AddMonoid.FG S] [IsCancelAdd S] [IsAddFree S]

variable (R S) in
noncomputable abbrev AffineToricVarietyFromMonoid := Spec <| CommRingCat.of (AddMonoidAlgebra R S)

noncomputable instance : (AffineToricVarietyFromMonoid R S).Over (Spec R) where
  hom := Spec.map <| CommRingCat.ofHom <| algebraMap R _

noncomputable instance : ToricVariety R (dim S) (AffineToricVarietyFromMonoid R S) where
  torusEmb := Spec.map <| CommRingCat.ofHom (AddMonoidMapLift <| AffineLatticeHom S).toRingHom
  torusEmb_comp_overHom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    simp [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  isOpenImmersion_torusEmb := sorry
  isDominant_torusEmb := sorry
  torusAct := (pullbackSpecIso _ _ _).hom ≫ (Spec.map <| CommRingCat.ofHom <| sorry)
  torusMul_comp_torusEmb := sorry
