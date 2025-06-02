/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Sophie Morel, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Sophie Morel, Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.AlgebraicGeometry.Limits
import Toric.GroupScheme.MonoidAlgebra
import Toric.Mathlib.Algebra.Group.TypeTags.Hom

open AlgebraicGeometry CategoryTheory Bialgebra Opposite Limits
open scoped AddMonoidAlgebra Hom

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme
section Diag
variable {S : Scheme.{u}} {M G : Type u} [AddCommMonoid M] [AddCommGroup G]

variable (S M) in
/-- The spectrum of a monoid algebra over an arbitrary base scheme `S`. -/
def Diag : Scheme.{u} :=
  pullback
    (Spec (.of <| MonoidAlgebra (ULift.{u} ℤ) <| Multiplicative M) ↘ Spec (.of <| ULift.{u} ℤ))
    (specULiftZIsTerminal.from S)

@[simps! -isSimp]
instance Diag.canonicallyOver : (Diag S M).CanonicallyOver S := by unfold Diag; infer_instance
instance : Mon_Class (asOver (Diag S M) S) := by unfold Diag; infer_instance
instance : Grp_Class (asOver (Diag S G) S) := by unfold Diag; infer_instance
instance : IsCommMon (asOver (Diag S M) S) := by unfold Diag; infer_instance

variable {R : CommRingCat.{u}}

variable (R M) in
def diagSpecIso : Diag (Spec R) M ≅ Spec (.of <| MonoidAlgebra R <| Multiplicative M) :=
  letI f := (algebraMap ℤ R).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom
  (isoWhiskerRight (specCommMonAlgPullback (CommRingCat.ofHom f) _
    (specULiftZIsTerminal.hom_ext _ _)) (Mon_.forget _ ⋙ Over.forget _)).app <|
      .op <| .of <| Multiplicative M

instance : (diagSpecIso M R).hom.IsOver (Spec R) where
  comp_over := by
    rw [← Iso.eq_inv_comp]
    exact (specCommMonAlgPullback_inv_app_hom_left_snd _ _ (specULiftZIsTerminal.hom_ext _ _) <|
      .op <| .of <| Multiplicative M).symm

instance : (diagSpecIso M R).inv.IsOver (Spec R) where
  comp_over := specCommMonAlgPullback_inv_app_hom_left_snd _ _
      (specULiftZIsTerminal.hom_ext _ _) <| .op <| .of <| Multiplicative M

instance : IsMon_Hom ((diagSpecIso M R).hom.asOver (Spec R)) :=
  letI f := (algebraMap ℤ R).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom
  Mon_.instIsMon_HomHom
  ((specCommMonAlgPullback (CommRingCat.ofHom f) (specULiftZIsTerminal.from _)
    (specULiftZIsTerminal.hom_ext _ _)).app <| .op <| .of <| Multiplicative M).hom

instance : IsMon_Hom ((diagSpecIso M R).inv.asOver (Spec R)) :=
  letI f := (algebraMap ℤ R).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom
  Mon_.instIsMon_HomHom
  ((specCommMonAlgPullback (CommRingCat.ofHom f) (specULiftZIsTerminal.from _)
    (specULiftZIsTerminal.hom_ext _ _)).app _).inv

variable (S) in
def diagMonFunctor : AddCommMonCatᵒᵖ ⥤ Mon_ (Over S) :=
  AddCommMonCat.equivalence.functor.op ⋙
    (commMonAlg (ULift.{u} ℤ)).op ⋙ bialgSpec (.of <| ULift.{u} ℤ) ⋙
      (Over.pullback (specULiftZIsTerminal.from S)).mapMon

@[simp] lemma diagMonFunctor_obj (M : AddCommMonCatᵒᵖ) :
    (diagMonFunctor S).obj M = .mk' ((Diag S M.unop).asOver S) := rfl

variable (S) in
def diagFunctor : AddCommGrpᵒᵖ ⥤ Grp_ (Over S) :=
  commGroupAddCommGroupEquivalence.inverse.op ⋙
    (commGrpAlg (ULift.{u} ℤ)).op ⋙ hopfSpec (.of <| ULift.{u} ℤ) ⋙
      (Over.pullback (specULiftZIsTerminal.from S)).mapGrp

@[simp] lemma diagFunctor_obj (M : AddCommGrpᵒᵖ) :
    (diagFunctor S).obj M = .mk' ((Diag S M.unop).asOver S) := rfl

instance {C : Type*} [Category C] {X : C} [CartesianMonoidalCategory C] [BraidedCategory C]
    [Grp_Class X] [IsCommMon X] : IsCommMon (Grp_.mk' X) :=
  letI : IsCommMon (Grp_.mk' X).X := ‹_›
  inferInstance

instance (M : AddCommMonCatᵒᵖ) : IsCommMon ((diagMonFunctor S).obj M).X :=
  inferInstanceAs (IsCommMon (asOver (Diag S M.unop) S))

instance (M : AddCommGrpᵒᵖ) : IsCommMon ((diagFunctor S).obj M).X :=
  inferInstanceAs (IsCommMon (asOver (Diag S M.unop) S))

@[simp]
lemma commHopfAlgCatEquivCogrpCommAlgCat_foo {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [HopfAlgebra R S] [HopfAlgebra R T] [Coalgebra.IsCocomm R S] (f g : S →ₐc[R] T) :
    (commHopfAlgCatEquivCogrpCommAlgCat _).functor.map (CommHopfAlgCat.ofHom (f * g)) =
      (((commHopfAlgCatEquivCogrpCommAlgCat _).functor.map (CommHopfAlgCat.ofHom f)).unop *
      ((commHopfAlgCatEquivCogrpCommAlgCat _).functor.map (CommHopfAlgCat.ofHom g)).unop).op := by
  apply Quiver.Hom.unop_inj
  ext1
  apply Quiver.Hom.unop_inj
  ext1
  convert_to f * g =
    (Algebra.TensorProduct.lift (AlgHomClass.toAlgHom f) (AlgHomClass.toAlgHom g)
      (fun _ _ ↦ .all _ _)).comp (Bialgebra.comulAlgHom _ _)
  dsimp [AlgHom.mul_def]
  rw [← AlgHom.comp_assoc]
  congr 1
  ext <;> simp

open Functor.LaxMonoidal Functor.Monoidal in
set_option maxHeartbeats 0 in
instance {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
    [CartesianMonoidalCategory D] (F : C ⥤ D)
    [BraidedCategory C] [BraidedCategory D] [F.Braided] : F.mapGrp.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
  { εIso := (Grp_.fullyFaithfulForget₂Mon_ _).preimageIso (εIso F.mapMon)
    μIso X Y := (Grp_.fullyFaithfulForget₂Mon_ _).preimageIso (μIso F.mapMon X.toMon_ Y.toMon_)
    μIso_hom_natural_left f Z := by convert μ_natural_left F.mapMon f Z.toMon_ using 1
    μIso_hom_natural_right Z f := by convert μ_natural_right F.mapMon Z.toMon_ f using 1
    associativity X Y Z := by convert associativity F.mapMon X.toMon_ Y.toMon_ Z.toMon_ using 1
    left_unitality X := by convert left_unitality F.mapMon X.toMon_ using 1
    right_unitality X := by convert right_unitality F.mapMon X.toMon_ using 1 }

lemma diagFunctor_map_add {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (f g : M →+ N) :
    (diagFunctor S).map (AddCommGrp.ofHom (f + g)).op =
      (diagFunctor S).map (AddCommGrp.ofHom f).op *
        (diagFunctor S).map (AddCommGrp.ofHom g).op := by
  simp [diagFunctor, Functor.map_mul]

variable (R) in
def diagMonFunctorIso :
    diagMonFunctor (Spec R) ≅ AddCommMonCat.equivalence.functor.op ⋙
      (commMonAlg R).op ⋙ bialgSpec R :=
  letI f := (algebraMap ℤ R).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom
  isoWhiskerLeft AddCommMonCat.equivalence.functor.op
    (specCommMonAlgPullback (CommRingCat.ofHom f) (specULiftZIsTerminal.from _)
      (specULiftZIsTerminal.hom_ext _ _))

lemma diagMonFunctorIso_app (M : AddCommMonCatᵒᵖ) :
    ((diagMonFunctorIso R).app M).hom.hom.left = (diagSpecIso M.unop _).hom := rfl

variable (R) in
def diagFunctorIso :
    diagFunctor (Spec R) ≅ commGroupAddCommGroupEquivalence.inverse.op ⋙
      (commGrpAlg R).op ⋙ hopfSpec R :=
  letI f := (algebraMap ℤ R).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom
  isoWhiskerLeft commGroupAddCommGroupEquivalence.inverse.op
    (specCommGrpAlgPullback (CommRingCat.ofHom f) (specULiftZIsTerminal.from _)
      (specULiftZIsTerminal.hom_ext _ _))

lemma diagFunctorIso_app (M : AddCommGrpᵒᵖ) :
    ((diagFunctorIso R).app M).hom.hom.left = (diagSpecIso M.unop _).hom := rfl

instance {R : Type*} [CommRing R] [IsDomain R] : (diagFunctor (Spec (.of R))).Full :=
  have : (hopfSpec (CommRingCat.of R)).Full := hopfSpec.instFull
  .of_iso (diagFunctorIso (.of R)).symm

instance {R : Type*} [CommRing R] [IsDomain R] : (diagFunctor (Spec (.of R))).Faithful :=
  have : (hopfSpec (CommRingCat.of R)).Faithful := hopfSpec.instFaithful
  .of_iso (diagFunctorIso (.of R)).symm

section

variable {G G' G'' S : Scheme.{u}} [G.Over S] [G'.Over S] [G''.Over S]
  [Grp_Class (G.asOver S)] [Grp_Class (G'.asOver S)] [Grp_Class (G''.asOver S)]

variable (G G' S) in
def HomGrp : Type u := Additive (Grp_.mk' (G.asOver S) ⟶ Grp_.mk' (G'.asOver S))

instance [IsCommMon (G'.asOver S)] : AddCommGroup (HomGrp G G' S) := by
  delta HomGrp; infer_instance

def HomGrp.ofHom (f : G ⟶ G') [f.IsOver S] [IsMon_Hom (f.asOver S)] : HomGrp G G' S :=
  Additive.ofMul (Grp_.homMk (f.asOver S))

def HomGrp.hom (f : HomGrp G G' S) : G ⟶ G' := f.toMul.hom.left

@[ext]
lemma HomGrp.toHom_injective : Function.Injective (HomGrp.hom (G := G) (G' := G') (S := S)) := by
  intros _ _ H; delta HomGrp; ext; exact H

def HomGrp.comp (f : HomGrp G G' S) (g : HomGrp G' G'' S) : HomGrp G G'' S :=
  .ofMul (f.toMul ≫ g.toMul)

instance {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {X Y : Grp_ C} [IsCommMon X.X] [IsCommMon Y.X] (f : X ⟶ Y) :
    IsMon_Hom f where
  one_hom := by ext; simp [Grp_.Hom.instMon_Class_toric]
  mul_hom := by ext; simp [Grp_.Hom.instMon_Class_toric]

lemma HomGrp.comp_add [IsCommMon (G'.asOver S)] [IsCommMon (G''.asOver S)]
    (f f' : HomGrp G G' S) (g : HomGrp G' G'' S) :
    (f + f').comp g = f.comp g + f'.comp g := by
  apply Additive.toMul.injective
  dsimp [HomGrp.comp, HomGrp]
  exact Mon_Class.mul_comp f.toMul f'.toMul g.toMul

@[simp]
lemma HomGrp.comp_zero [IsCommMon (G''.asOver S)]
    (f : HomGrp G G' S) : f.comp (0 : HomGrp G' G'' S) = 0 := by
  apply Additive.toMul.injective
  dsimp [HomGrp.comp, HomGrp]
  exact Mon_Class.comp_one _

@[simp]
lemma HomGrp.zero_comp [IsCommMon (G'.asOver S)] [IsCommMon (G''.asOver S)]
    (f : HomGrp G' G'' S) : (0 : HomGrp G G' S).comp f = 0 := by
  apply Additive.toMul.injective
  dsimp [HomGrp.comp, HomGrp]
  exact Mon_Class.one_comp f.toMul

lemma HomGrp.add_comp [IsCommMon (G''.asOver S)]
    (f : HomGrp G G' S) (g g' : HomGrp G' G'' S) :
    f.comp (g + g') = f.comp g + f.comp g' := by
  apply Additive.toMul.injective
  dsimp [HomGrp.comp, HomGrp]
  exact Mon_Class.comp_mul _ _ _

end

variable (S) in
set_option maxHeartbeats 0 in
def diagHomGrp {M N : Type u} [AddCommGroup M] [AddCommGroup N] (f : M →+ N) :
    HomGrp (Diag S N) (Diag S M) S := .ofMul ((diagFunctor S).map (AddCommGrp.ofHom f).op)

set_option maxHeartbeats 0 in
lemma diagHomGrp_comp {M N O : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    (f : M →+ N) (g : N →+ O) :
    (diagHomGrp S g).comp (diagHomGrp S f) = diagHomGrp S (g.comp f) := by
  apply Additive.toMul.injective
  dsimp [HomGrp, diagHomGrp, HomGrp.comp]
  exact (S.diagFunctor.map_comp ..).symm

set_option maxHeartbeats 0 in
lemma diagHomGrp_comp_add {M N O : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    (f f' : M →+ N) (g : N →+ O) :
    (diagHomGrp S g).comp (diagHomGrp S f) = diagHomGrp S (g.comp f) := by
  apply Additive.toMul.injective
  dsimp [HomGrp, diagHomGrp, HomGrp.comp]
  exact (S.diagFunctor.map_comp ..).symm

set_option maxHeartbeats 0 in
def diagHomEquiv {R M N : Type u} [CommRing R] [IsDomain R] [AddCommGroup M] [AddCommGroup N] :
    (N →+ M) ≃+ HomGrp (Diag (Spec (.of R)) M) (Diag (Spec (.of R)) N) (Spec (.of R)) :=
  letI e := Functor.FullyFaithful.homEquiv (.ofFullyFaithful (diagFunctor (Spec <| .of R)))
    (X := .op (.of M)) (Y := .op (.of N))
  { toFun f := Additive.ofMul (e (AddCommGrp.ofHom f).op)
    invFun f := (e.symm f.toMul).unop.hom
    left_inv _ := by simp only [toMul_ofMul, e.symm_apply_apply]; rfl
    right_inv _ := by simp only [AddCommGrp.ofHom_hom, Quiver.Hom.op_unop, e.apply_symm_apply,
      ofMul_toMul]
    map_add' f g := congr(Additive.ofMul $(diagFunctor_map_add f g))  }

lemma diagHomEquiv_apply {R M N : Type u}
    [CommRing R] [IsDomain R] [AddCommGroup M] [AddCommGroup N] (f : N →+ M) :
    diagHomEquiv (R := R) f = diagHomGrp (Spec _) f := rfl

end Diag

section Scheme
variable {S G H : Scheme.{u}} [G.Over S] [H.Over S] [Grp_Class (asOver G S)]
  [Grp_Class (asOver H S)]

variable (S G) in
@[mk_iff]
class IsDiagonalisable : Prop where
  existsIso :
    ∃ (A : Type u) (_ : AddCommGroup A),
      Nonempty <| Grp_.mk' (asOver G S) ≅ .mk' (asOver (Diag S A) S)

instance {A : Type u} [AddCommGroup A] : IsDiagonalisable S (Diag S A) :=
  ⟨A, ‹_›, ⟨by exact .refl _⟩⟩

lemma IsDiagonalisable.ofIso [IsDiagonalisable S H]
    (e : Grp_.mk' (asOver G S) ≅ .mk' (asOver H S)) : IsDiagonalisable S G :=
  let ⟨A, _, ⟨e'⟩⟩ := ‹IsDiagonalisable S H›; ⟨A, _, ⟨e.trans e'⟩⟩

instance  (f : G ⟶ H) [IsIso f] [f.IsOver S] : IsIso (f.asOver S) :=
  have : IsIso ((Over.forget S).map (Hom.asOver f S)) := ‹_›
  isIso_of_reflects_iso _ (Over.forget _)

lemma IsDiagonalisable.of_isIso [IsDiagonalisable S H]
    (f : G ⟶ H) [IsIso f] [f.IsOver S] [IsMon_Hom (f.asOver S)] : IsDiagonalisable S G :=
  have : IsMon_Hom (asIso (Hom.asOver f S)).hom := ‹_›
  IsDiagonalisable.ofIso (H := H) ((Grp_.fullyFaithfulForget₂Mon_ _).preimageIso
    (Mon_.mkIso' (asIso (f.asOver S))))

end Scheme

section CommRing
variable {R : CommRingCat.{u}} {G : Scheme.{u}} [G.Over (Spec R)] [Grp_Class (asOver G (Spec R))]
  {A : Type u} [AddCommGroup A]

instance : IsDiagonalisable (Spec R) (Spec <| .of R[A]) := .of_isIso (diagSpecIso A R).inv

variable [IsDomain R]

/-- An affine algebraic group `G` over a domain `R` is diagonalisable iff it is affine and `Γ(G)` is
`R`-spanned by its group-like elements.

Note that this is more generally true over arbitrary commutative rings, but we do not prove that.
See SGA III, Exposé VIII for more info.

Note that more generally a not necessarily affine algebraic group `G` over a field `K` is
diagonalisable iff it is affine and `Γ(G)` is `K`-spanned by its group-like elements, but we do not
prove that. -/
lemma isDiagonalisable_iff_span_isGroupLikeElem_eq_top [IsAffine G] :
    IsDiagonalisable (Spec R) G ↔ Submodule.span R {a : Γ(G, ⊤) | IsGroupLikeElem R a} = ⊤ :=
  sorry

end CommRing
end AlgebraicGeometry.Scheme
