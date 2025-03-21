/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.Algebra.Category.Ring.Under.Basic
import Toric.Mathlib.AlgebraicGeometry.AffineScheme
import Toric.Mathlib.CategoryTheory.ChosenFiniteProducts.Over
import Toric.Mathlib.CategoryTheory.Limits.Preserves.Finite
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_

/-!
# The equivalence between Hopf algebras and affine group schemes

This file constructs `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`,
shows it is full and faithful, and has affine group schemes as essential image.

We want to show that Hopf algebras correspond to affine group schemes. This can easily be done
categorically assuming both categories on either side are defined thoughtfully. However, the
categorical version will not be workable with if we do not also have links to the non-categorical
notions. Therefore, we will build the left, top and right edges of the following diagram so that
the bottom edge can be obtained by composing the three.

```
   Cogrp Mod_R →     Grp Sch_{Spec R}
        ↓                    ↓
R-Hopf algebra → Group scheme over Spec R
```
-/

open AlgebraicGeometry CategoryTheory Opposite Limits

attribute [local instance] Over.chosenFiniteProducts -- From #21399

variable {R : CommRingCat}

/-!
### Top edge: equivalence of categories

In this section we show that the category of cogroup objects of rings under a ring `R` is equivalent
 to the category of group objects of schemes over `Spec R`.
-/

noncomputable def algEquivSch : (Under R)ᵒᵖ ≌ Over <| AffineScheme.Spec.obj <| .op R :=
  (Over.opEquivOpUnder R).symm.trans <|
    Over.postEquiv (.op R) AffineScheme.equivCommRingCat.symm

noncomputable def hopfAlgEquivAffGrpSch :
    Grp_ (Under R)ᵒᵖ ≌ Grp_ (Over <| AffineScheme.Spec.obj <| .op R) :=
  .mapGrp algEquivSch

variable (R) in
/-- `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`. -/
noncomputable abbrev hopfSpec : Grp_ (Under R)ᵒᵖ ⥤ Grp_ (Over <| Spec R) :=
  (((Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec).mapGrp:)

/-- `Spec` is full on `R`-Hopf algebras. -/
instance hopfSpec.instFull : (hopfSpec R).Full := inferInstance

/-- `Spec` is faithful on `R`-Hopf algebras. -/
instance hopfSpec.instFaithful : (hopfSpec R).Faithful := inferInstance

/-!
### Left edge: `R`-Hopf algebras correspond to cogroup objects under `R`

In this section, we provide ways to turn an unbundled `R`-Hopf algebra into a bundled cogroup
object under `R`, and vice versa.
-/

section Michal

variable {R : CommRingCat} {A : Type*}
namespace HopfAlgebra

section
variable [Semiring A] [HopfAlgebra R A]

lemma antipode_anti_comm (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) b * antipode (R := R) a := by
  sorry
end

section
variable [CommRing A] [HopfAlgebra R A]

lemma antipode_comm (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) a * antipode (R := R) b := by
  rw [antipode_anti_comm a b, mul_comm]

end

end HopfAlgebra

variable [CommRing A] [HopfAlgebra R A]

open CommRingCat MonoidalCategory

variable (A) in
noncomputable def UnderOp.Unitor.ringHom := (Algebra.TensorProduct.lid R A).symm.toAlgHom

-- (UnderOp.Unitor.ringHom A).toRingHom
example : toAlgHom (unop (λ_ (op (R.mkUnder A))).hom) =
    (Algebra.TensorProduct.map (.mk (R := R) (.id R) (fun _ ↦ rfl)) (.mk (R := R) (.id A) (fun _ ↦ rfl)))
      ∘ (Algebra.TensorProduct.lid R A).symm.toAlgHom
    := by
  sorry

noncomputable def UnderOp.Unitor.hom : 𝟙_ (Under R)ᵒᵖ ⊗ op (R.mkUnder A) ⟶ op (R.mkUnder A) := by
  apply op
  change R.mkUnder A ⟶ _
  refine (Algebra.TensorProduct.lid R A).symm.toAlgHom.toUnder ≫
      (Algebra.TensorProduct.map ?_ ?_).toUnder
  · exact .mk (.id R) (fun _ ↦ rfl)
  exact .mk (.id A) (fun _ ↦ rfl)

lemma UnderOp.Unitor.hom_eq : (λ_ (op (R.mkUnder A))).hom = UnderOp.Unitor.hom := rfl

noncomputable def UnderOp.RightWhisker.hom :
  op { left := { as := PUnit.unit }, right := of ↑R, hom := ofHom (algebraMap ↑R ↑R) } ⊗ op (R.mkUnder A) ⟶
  op { left := { as := PUnit.unit }, right := of A, hom := ofHom (algebraMap (↑R) A) } ⊗ op (R.mkUnder A) := by
  apply op
  change unop (op (R.mkUnder A) ⊗ _) ⟶ unop ((op (Under.mk (𝟙 R))) ⊗ _)
  refine (Algebra.TensorProduct.map ?_ ?_).toUnder
  · exact @AlgHom.mk _ _ _ _ _ _ _ (_) ((Bialgebra.counitAlgHom R A).toRingHom) (Bialgebra.counitAlgHom (↑R) A).commutes'
  exact @AlgHom.mk _ _ _ _ _ _ _ (_) (.id _) fun _ ↦ rfl

example : op (Bialgebra.counitAlgHom (↑R) A).toUnder ▷ op (R.mkUnder A) = UnderOp.RightWhisker.hom := by
  simp [UnderOp.RightWhisker.hom]
  ext
  · simp
    sorry
  sorry

noncomputable instance : Grp_Class <| op <| CommRingCat.mkUnder R A where
  one := op <| (Bialgebra.counitAlgHom R A).toUnder
  mul := op <| by
    refine (Bialgebra.comulAlgHom R A).toUnder ≫ (Algebra.TensorProduct.map ?_ ?_).toUnder <;>
      exact @AlgHom.mk _ _ _ _ _ _ _ (_) (.id _) fun _ ↦ rfl
  one_mul' := by
    rw [UnderOp.Unitor.hom_eq, UnderOp.Unitor.hom]
    rw [← unop_inj_iff]
    simp
    sorry
  mul_one' := sorry
  mul_assoc' := sorry
  inv := sorry
  left_inv' := sorry
  right_inv' := sorry

end Michal

/-!
### Right edge: Group schemes corresponds to group objects in the category of schemes

Mathlib already provides tooling for turning a bundled group objects into an unbundled group object
and back, so there is nothing to be done here.

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
