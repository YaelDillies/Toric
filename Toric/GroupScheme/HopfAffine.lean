/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Toric.Mathlib.Algebra.Category.CommHopfAlgCat
import Toric.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

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

open AlgebraicGeometry Coalgebra Scheme CategoryTheory MonoidalCategory Functor Monoidal Opposite
  Limits Mon_Class Grp_Class TensorProduct

universe u
variable {R : CommRingCat.{u}}

/-!
### Left edge: `R`-Hopf algebras correspond to cogroup objects under `R`

Ways to turn an unbundled `R`-Hopf algebra into a bundled cogroup object under `R`, and vice versa,
are already provided in `Toric.Mathlib.Algebra.Category.CommHopfAlgCat`.

### Top edge: `Spec` as a functor on Hopf algebras

In this section we construct `Spec` as a functor from `R`-Hopf algebras to affine group schemes over
`Spec R`.
-/

section topEdge

variable (R) in
/-- `Spec` as a functor from `R`-algebras to schemes over `Spec R`. -/
noncomputable abbrev algSpec : (CommAlgCat R)ᵒᵖ ⥤ Over (Spec R) :=
  (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

-- FIXME: Neither `inferInstance` nor `by unfold algSpec; infer_instance` work in the following 3.
-- TODO: Do a MWE once `CommAlgCat` is in mathlib
instance preservesLimits_algSpec : PreservesLimits (algSpec R) :=
  inferInstanceAs <| PreservesLimits <|
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

noncomputable instance braidedAlgSpec : (algSpec R).Braided := .ofChosenFiniteProducts _

@[simp]
lemma δ_algSpec_inv_left (A B : (CommAlgCat R)ᵒᵖ) :
    (OplaxMonoidal.δ (algSpec R) A B).left = (pullbackSpecIso R A.unop B.unop).inv := rfl

-- arguably this should be defeq.
lemma μ_algSpec_left (A B : (CommAlgCat R)ᵒᵖ) :
    (LaxMonoidal.μ (algSpec R) A B).left = (pullbackSpecIso R A.unop B.unop).hom := by
  rw [← Iso.comp_inv_eq_id, ← δ_algSpec_inv_left, ← Over.comp_left, Monoidal.μ_δ, Over.id_left]

-- arguably this should be defeq.
@[simp]
lemma η_algSpec_inv_left : (OplaxMonoidal.η (algSpec R)).left = 𝟙 (Spec R) := by
  refine (Category.comp_id _).symm.trans ((OplaxMonoidal.η (algSpec R)).w.trans ?_)
  simp
  rfl

-- arguably this should be defeq.
@[simp]
lemma ε_algSpec_left : (LaxMonoidal.ε (algSpec R)).left = 𝟙 (Spec R) := by
  rw [← Category.comp_id (CommaMorphism.left _)]
  dsimp [CommRingCat.mkUnder]
  rw [← η_algSpec_inv_left, ← Over.comp_left]
  exact congr($(Monoidal.ε_η (F := algSpec R)).left)

@[simp]
lemma prodComparisonIso_algSpec_hom_left (A B : (CommAlgCat R)ᵒᵖ) :
    (CartesianMonoidalCategory.prodComparisonIso (algSpec R) A B).hom.left =
      (pullbackSpecIso R A.unop B.unop).inv := rfl

@[simp]
lemma prodComparisonIso_algSpec_inv_left (A B : (CommAlgCat R)ᵒᵖ) :
    (CartesianMonoidalCategory.prodComparisonIso (algSpec R) A B).inv.left =
      (pullbackSpecIso R A.unop B.unop).hom := by
  rw [← Iso.comp_inv_eq_id, ← prodComparisonIso_algSpec_hom_left, ← Over.comp_left,
    Iso.inv_hom_id, Over.id_left]

lemma preservesTerminalIso_algSpec :
  (CartesianMonoidalCategory.preservesTerminalIso (algSpec R)) =
    Over.isoMk (Iso.refl (Spec R)) (by dsimp; simp [MonoidalCategoryStruct.tensorUnit]) := by
  ext1; exact CartesianMonoidalCategory.toUnit_unique _ _

@[simp]
lemma preservesTerminalIso_algSpec_inv_left :
  (CartesianMonoidalCategory.preservesTerminalIso (algSpec R)).inv.left = 𝟙 (Spec R) := by
  simp [preservesTerminalIso_algSpec]

@[simp]
lemma preservesTerminalIso_algSpec_hom_left :
  (CartesianMonoidalCategory.preservesTerminalIso (algSpec R)).hom.left = 𝟙 (Spec R) := by
  simp [preservesTerminalIso_algSpec]

/-- `Spec` is full on `R`-algebras. -/
instance full_algSpec : (algSpec R).Full :=
  inferInstanceAs <| Functor.Full <|
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is faithful on `R`-algebras. -/
instance faithful_algSpec : (algSpec R).Faithful :=
  inferInstanceAs <| Functor.Faithful <|
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is fully faithful on `R`-algebras, with inverse `Gamma`. -/
noncomputable def fullyFaithfulAlgSpec : (algSpec R).FullyFaithful :=
  ((commAlgCatEquivUnder R).op.trans (Over.opEquivOpUnder R).symm).fullyFaithfulFunctor.comp <|
    Spec.fullyFaithful.over _

variable (R) in
/-- `Spec` as a functor from `R`-bialgebras to monoid schemes over `Spec R`. -/
noncomputable abbrev bialgSpec : (CommBialgCat R)ᵒᵖ ⥤ Mon_ (Over <| Spec R) :=
  (commBialgCatEquivComonCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapMon

variable (R) in
/-- `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`. -/
noncomputable abbrev hopfSpec : (CommHopfAlgCat R)ᵒᵖ ⥤ Grp_ (Over <| Spec R) :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapGrp

/-- `Spec` is full on `R`-Hopf algebras. -/
instance full_hopfSpec : (hopfSpec R).Full := inferInstance

/-- `Spec` is faithful on `R`-Hopf algebras. -/
instance faithful_hopfSpec : (hopfSpec R).Faithful := inferInstance

/-- `Spec` is fully faithful on `R`-Hopf algebras, with inverse `Gamma`. -/
noncomputable def fullyFaithfulHopfSpec : (hopfSpec R).FullyFaithful :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).fullyFaithfulFunctor.leftOp.comp
    fullyFaithfulAlgSpec.mapGrp

namespace AlgebraicGeometry.Scheme
variable {R A : Type u} [CommRing R] [CommRing A]

suppress_compilation

instance SpecOverSpec [Algebra R A] : (Spec <| .of A).Over (Spec <| .of R) where
  hom := Spec.map <| CommRingCat.ofHom <| algebraMap ..

lemma over_Spec_Spec [Algebra R A] :
  Spec (.of A) ↘ Spec (.of R) = Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl

instance Mon_ClassAsOverSpecSpec [Bialgebra R A] :
    Mon_Class (asOver (Spec (.of A)) (Spec (.of R))) :=
  ((bialgSpec (.of R)).obj <| .op <| .of R A).instMon_ClassX

lemma one_left [Bialgebra R A] :
    η[asOver (Spec (.of A)) (Spec (.of R))].left =
      Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R A)) := by
  show _ ≫ _ = _
  rw [ε_algSpec_left]
  rfl

lemma mul_left [Bialgebra R A] :
    μ[asOver (Spec (.of A)) (Spec (.of R))].left = (pullbackSpecIso R A A).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R A)) := by
  show _ ≫ _ = _
  rw [μ_algSpec_left]
  rfl

instance isCommMon_asOver_Spec_Spec [Bialgebra R A] [IsCocomm R A] :
    IsCommMon (asOver (Spec (.of A)) (Spec (.of R))) where
  mul_comm' := by
    ext
    have := congr((pullbackSpecIso R A A).hom ≫ ((bialgSpec (.of R)).map <| .op <|
      CommBialgCat.ofHom <| $(Bialgebra.comm_comp_comulBialgHom R A)).hom.left)
    dsimp [AlgHom.toUnder, AlgHom.comp_toRingHom] at this ⊢
    have h₁ : (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) =
      (RingHomClass.toRingHom (Bialgebra.comm R A A)).comp
        Algebra.TensorProduct.includeLeftRingHom := by ext; rfl
    have h₂ : (Algebra.TensorProduct.includeLeftRingHom) =
      (RingHomClass.toRingHom (Bialgebra.comm R A A)).comp
       (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) := by ext; rfl
    convert this using 1
    · simp only [Spec.map_comp, ← Category.assoc, mul_left]
      congr 1
      rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
      ext
      · simp [AlgHom.toUnder, over_Spec_Spec, h₁]; rfl
      · simp [AlgHom.toUnder, over_Spec_Spec, h₂]; rfl
    · exact mul_left ..

instance asOver.instGrp_Class [HopfAlgebra R A] :
    Grp_Class (asOver (Spec (.of A)) (Spec (.of R))) :=
  ((hopfSpec (.of R)).obj <| .op <| .of R A).instGrp_ClassX

lemma neg_left [HopfAlgebra R A] :
    ι[asOver (Spec (.of A)) (Spec (.of R))].left =
      Spec.map (CommRingCat.ofHom (HopfAlgebra.antipodeAlgHom R A)) := rfl

instance asOver.instCommGrp_Class [HopfAlgebra R A] [IsCocomm R A] :
   CommGrp_Class (asOver (Spec (.of A)) (Spec (.of R))) where

end AlgebraicGeometry.Scheme

end topEdge

/-!
### Right edge: The essential image of `Spec` on Hopf algebras

In this section we show that the essential image of `R`-Hopf algebras under `Spec` is precisely
affine group schemes over `Spec R`.
-/

section rightEdge

/-- The essential image of `R`-algebras under `Spec` is precisely affine schemes over `Spec R`. -/
@[simp]
lemma essImage_algSpec {G : Over <| Spec R} : (algSpec R).essImage G ↔ IsAffine G.left := by
  simp [algSpec, Functor.essImage_overPost]
  rw [Functor.essImage_overPost] -- not sure why `simp` doesn't use this already
  simp

/-- The essential image of `R`-Hopf algebras under `Spec` is precisely affine group schemes over
`Spec R`. -/
@[simp]
lemma essImage_hopfSpec {G : Grp_ (Over <| Spec R)} :
    (hopfSpec R).essImage G ↔ IsAffine G.X.left := by simp

end rightEdge
