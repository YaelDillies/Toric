/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib
import Toric.Hopf.CommAlg
import Toric.Mathlib.Algebra.Category.Ring.Under.Basic
import Toric.Mathlib.AlgebraicGeometry.AffineScheme
import Toric.Mathlib.CategoryTheory.ChosenFiniteProducts.Over
import Toric.Mathlib.CategoryTheory.Comma.Over.Basic
import Toric.Mathlib.CategoryTheory.Limits.Preserves.Finite
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The equivalence between Hopf algebras and affine group schemes

This file constructs `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`,
shows it is full and faithful, and has affine group schemes as essential image.

We want to show that Hopf algebras correspond to affine group schemes. This can easily be done
categorically assuming both categories on either side are defined thoughtfully. However, the
categorical version will not be workable with if we do not also have links to the non-categorical
notions. Therefore, one solution would be to build the left, top and right edges of the following
diagram so that the bottom edge can be obtained by composing the three.

```
  Cogrp Mod_R ≌ Grp AffSch_{Spec R} ≌ Aff Grp Sch_{Spec R}
      ↑ ↓                                      ↑ ↓
R-Hopf algebras         ≃       Affine group schemes over Spec R
```

If we do not care about going back from affine group schemes over `Spec R` to `R`-Hopf algebras
(eg because all our affine group schemes are given as the `Spec` of some algebra), then we can
follow the following simpler diagram:

```
  Cogrp Mod_R   ⥤        Grp Sch_{Spec R}
      ↑ ↓                        ↓
R-Hopf algebras → Affine group schemes over Spec R
```
where the top `≌` comes from the essentially surjective functor `Cogrp Mod_R ⥤ Grp Sch_{Spec R}`,
so that in particular we do not easily know that its inverse is given by `Γ`.
-/

open AlgebraicGeometry Scheme CategoryTheory Opposite Limits

attribute [local instance] Over.chosenFiniteProducts -- From #21399

universe u
variable {R : CommRingCat.{u}}

/-!
### Top edge: equivalence of categories
-/

variable (R) in
/-- `Spec` as a functor from `R`-algebras to schemes over `Spec R`. -/
noncomputable abbrev algSpec : (CommAlg R)ᵒᵖ ⥤ Over (Spec R) :=
  (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

-- FIXME: Neither `inferInstance` nor `by unfold algSpec; infer_instance` work in the following 3.
-- TODO: Do a MWE once `CommAlg` is in mathlib
instance algSpec.instPreservesLimits : PreservesLimits (algSpec R) :=
  inferInstanceAs <| PreservesLimits <|
    (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is full on `R`-algebras. -/
instance algSpec.instFull : (algSpec R).Full :=
  inferInstanceAs <| Functor.Full <|
    (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is faithful on `R`-algebras. -/
instance algSpec.instFaithful : (algSpec R).Faithful :=
  inferInstanceAs <| Functor.Faithful <|
    (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is fully faithful on `R`-algebras, with inverse `Gamma`. -/
noncomputable def algSpec.fullyFaithful : (algSpec R).FullyFaithful :=
  ((commAlgEquivUnder R).op.trans (Over.opEquivOpUnder R).symm).fullyFaithfulFunctor.comp <|
    Spec.fullyFaithful.over _

variable (R) in
/-- `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`. -/
noncomputable abbrev hopfSpec : Grp_ (CommAlg R)ᵒᵖ ⥤ Grp_ (Over <| Spec R) := (algSpec R).mapGrp

/-- `Spec` is full on `R`-Hopf algebras. -/
instance hopfSpec.instFull : (hopfSpec R).Full := inferInstance

/-- `Spec` is faithful on `R`-Hopf algebras. -/
instance hopfSpec.instFaithful : (hopfSpec R).Faithful := inferInstance

/-- `Spec` is fully faithful on `R`-Hopf algebras, with inverse `Gamma`. -/
noncomputable def hopfSpec.fullyFaithful : (hopfSpec R).FullyFaithful :=
  algSpec.fullyFaithful.mapGrp

/-!
### Left edge: `R`-Hopf algebras correspond to cogroup objects under `R`

In this section, we provide ways to turn an unbundled `R`-Hopf algebra into a bundled cogroup
object under `R`, and vice versa.
-/

section Michal
variable {R : CommRingCat} {A : Type*} [CommRing A] [HopfAlgebra R A]

open CommRingCat

noncomputable instance : Grp_Class <| op <| CommRingCat.mkUnder R A where
  one := op <| (Bialgebra.counitAlgHom R A).toUnder
  mul := op <| by
    refine (Bialgebra.comulAlgHom R A).toUnder ≫ (Algebra.TensorProduct.map ?_ ?_).toUnder <;>
      exact @AlgHom.mk _ _ _ _ _ _ _ (_) (.id _) fun _ ↦ rfl
  one_mul' := sorry
  mul_one' := sorry
  mul_assoc' := sorry
  inv := sorry
  left_inv' := sorry
  right_inv' := sorry

end Michal

/-!
### Right edge: The category of group affine schemes is equivalent to that of affine group schemes
-/
variable (R) in
/-- The category of affine group schemes over `Spec R`. -/
abbrev AffGrpOverSpec := (hopfSpec R).EssImageSubcategory

/-- Group affine schemes are equivalent to affine group schemes -/
def GrpAffOverSpecEquivAffGrpOverSpec : Grp_ (Over <| Spec R) ≅ AffGrpOverSpec R := sorry

/-!
### Bottom edge: transferring between unbundled objects

In this section we provide ways to turn an unbundled `R`-Hopf algebra into an unbundled group
scheme over `R`, and vice-verse.
-/

noncomputable instance Gamma.instAlgebra (G : Scheme) [OverClass G (Spec R)] : Algebra R Γ(G, ⊤) :=
  RingHom.toAlgebra <| CommRingCat.Hom.hom <| (Scheme.ΓSpecIso R).inv ≫ Scheme.Γ.map (G ↘ Spec R).op

/-- For an `R`-algebraic group `G`, this is the global sections `Γ(G)` as a `R`-algebra. -/
noncomputable abbrev algebraGamma (G : Over <| Spec R) [Grp_Class G] : Under R :=
  .mk <| CommRingCat.ofHom <| algebraMap R Γ(G.left, ⊤)

instance (G : Over <| Spec R) [Grp_Class G] : Grp_Class (op <| algebraGamma G) := sorry

-- Yaël: I think this technically belongs to the top edge?
/-- The essential image of `R`-Hopf algebras under `Spec` is precisely affine group schemes over
`Spec R`. -/
@[simp]
lemma essImage_hopfSpec {G : Grp_ (Over <| Spec R)} :
    (hopfSpec R).essImage G ↔ IsAffine G.X.left where
  mp hG := by
    let e : G.X.left ⟶ Spec hG.witness.X.unop.right := ((Grp_.forget _).map hG.getIso.inv).left
    exact .of_isIso e
  mpr _ := by
    refine ⟨.mk' <| .op <| algebraGamma G.X,
      ⟨Grp_.mkIso (Over.isoMk G.X.left.isoSpec.symm ?_) ?_ ?_⟩⟩
    · simp
      sorry
    · ext : 1
      simp
      sorry
    · sorry

/-!
### Left top edge: equivalence of categories

In this section we show that the category of cogroup objects of rings under a ring `R` is equivalent
to the category of group objects of affine schemes over `Spec R`.
-/

/-- The category of `R`-algebras is equivalence to the category of affine schemes over `Spec R`. -/
@[simps! functor inverse]
noncomputable def algEquivSch : (Under R)ᵒᵖ ≌ Over <| AffineScheme.Spec.obj <| .op R :=
  (Over.opEquivOpUnder R).symm.trans <| Over.postEquiv (.op R) AffineScheme.equivCommRingCat.symm

/-- The category of `R`-Hopf algebras is equivalent to the category of group affine schemes over
`Spec R`. -/
@[simps! functor inverse]
noncomputable def hopfAlgEquivGrpAffSch :
    Grp_ (Under R)ᵒᵖ ≌ Grp_ (Over <| AffineScheme.Spec.obj <| .op R) := algEquivSch.mapGrp

/-!
### Right edge: The category of group affine schemes is equivalent to that of affine group schemes
-/

/-- Group affine schemes are equivalent to affine group schemes -/
def GrpAffOverSpecEquivAffGrpOverSpec : Grp_ (Over <| Spec R) ≅ AffGrpOverSpec R := sorry
