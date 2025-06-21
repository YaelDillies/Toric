/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Sophie Morel, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Sophie Morel, Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Toric.GroupScheme.MonoidAlgebra
import Toric.Mathlib.Algebra.Group.TypeTags.Hom
import Toric.Mathlib.AlgebraicGeometry.Scheme
import Toric.Mathlib.CategoryTheory.Comma.Over.OverClass

open AlgebraicGeometry CategoryTheory Bialgebra Opposite Limits
open scoped AddMonoidAlgebra Mon_Class

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme
section Diag
variable {S T : Scheme.{u}} {R : CommRingCat.{u}} {M N O G : Type u} [AddCommMonoid M]
  [AddCommMonoid N] [AddCommMonoid O] [AddCommGroup G]

variable (S) in
def diagMonFunctor : AddCommMonCatᵒᵖ ⥤ Mon_ (Over S) :=
  AddCommMonCat.equivalence.functor.op ⋙
    (commMonAlg (ULift.{u} ℤ)).op ⋙ bialgSpec (.of <| ULift.{u} ℤ) ⋙
      (Over.pullback (specULiftZIsTerminal.from S)).mapMon

variable (S M) in
/-- The spectrum of a monoid algebra over an arbitrary base scheme `S`. -/
def Diag : Scheme.{u} :=
  pullback
    (Spec(MonoidAlgebra (ULift.{u} ℤ) <| Multiplicative M) ↘ Spec(ULift.{u} ℤ))
    (specULiftZIsTerminal.from S)

@[simps! -isSimp]
instance Diag.canonicallyOver : (Diag S M).CanonicallyOver S := by unfold Diag; infer_instance
@[simps! -isSimp one_left mul_left]
instance Diag.mon_ClassAsOver : Mon_Class (asOver (Diag S M) S) := by unfold Diag; infer_instance
@[simps! -isSimp inv_left]
instance Diag.grp_ClassAsOver : Grp_Class (asOver (Diag S G) S) := by unfold Diag; infer_instance
instance Diag.isCommMon_asOver : IsCommMon (asOver (Diag S M) S) := by unfold Diag; infer_instance

@[simp] lemma diagMonFunctor_obj (M : AddCommMonCatᵒᵖ) :
    (diagMonFunctor S).obj M = .mk ((Diag S M.unop).asOver S) := rfl

variable (S) in
/-- A monoid hom `M → N` induces a monoid morphism `Diag S N ⟶ Diag S M`. -/
def Diag.map (f : M →+ N) : Diag S N ⟶ Diag S M :=
  pullback.map _ _ _ _
    (Spec.map <| CommRingCat.ofHom <| MonoidAlgebra.mapDomainRingHom _ f.toMultiplicative)
    (𝟙 S) (𝟙 _) (by simp [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) (by simp)

attribute [local simp] Diag.map Diag.canonicallyOver_over in
instance Diag.isOver_map {f : M →+ N} : (Diag.map S f).IsOver S where

instance Diag.isMon_Hom_map {f : M →+ N} : IsMon_Hom <| (Diag.map S f).asOver S :=
  inferInstanceAs <| IsMon_Hom <| ((diagMonFunctor S).map <| .op <| AddCommMonCat.ofHom f).hom

@[simp] lemma diagMonFunctor_map {M N : AddCommMonCatᵒᵖ} (f : M ⟶ N) :
    (diagMonFunctor S).map f = .mk ((Diag.map S f.unop.hom).asOver S) := rfl

variable (S M) in
@[simp] lemma Diag.map_id : Diag.map S (.id M) = 𝟙 (Diag S M) := by simp [Diag.map]; rfl

variable (S) in
@[simp] lemma Diag.map_comp (f : N →+ O) (g : M →+ N) :
    Diag.map S (f.comp g) = Diag.map S f ≫ Diag.map S g :=
  congr(($((diagMonFunctor S).map_comp (.op <| AddCommMonCat.ofHom f)
    (.op <| AddCommMonCat.ofHom g))).hom.left)

variable (S) in
/-- A monoid iso `M ≃ N` induces a monoid isomorphism `Diag S M ≅ Diag S N`. -/
@[simps]
def Diag.mapIso (f : M ≃+ N) : Diag S M ≅ Diag S N where
  hom := Diag.map S f.symm
  inv := Diag.map S f
  hom_inv_id := by simp [← Diag.map_comp]
  inv_hom_id := by simp [← Diag.map_comp]

variable (R M) in
def diagSpecIso : Diag (Spec R) M ≅ Spec(MonoidAlgebra R <| Multiplicative M) :=
  letI f := (algebraMap ℤ R).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom
  (isoWhiskerRight (specCommMonAlgPullback (CommRingCat.ofHom f) _
    (specULiftZIsTerminal.hom_ext _ _)) (Mon_.forget _ ⋙ Over.forget _)).app <|
      .op <| .of <| Multiplicative M

instance isOver_diagSpecIso_hom : (diagSpecIso R M).hom.IsOver (Spec R) where
  comp_over := by
    rw [← Iso.eq_inv_comp]
    exact (specCommMonAlgPullback_inv_app_hom_left_snd _ _ (specULiftZIsTerminal.hom_ext _ _) <|
      .op <| .of <| Multiplicative M).symm

instance isOver_diagSpecIso_inv : (diagSpecIso R M).inv.IsOver (Spec R) where
  comp_over := specCommMonAlgPullback_inv_app_hom_left_snd _ _
      (specULiftZIsTerminal.hom_ext _ _) <| .op <| .of <| Multiplicative M

instance : IsMon_Hom ((diagSpecIso R M).hom.asOver (Spec R)) :=
  letI f := (algebraMap ℤ R).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom
  Mon_.instIsMon_HomHom
  ((specCommMonAlgPullback (CommRingCat.ofHom f) (specULiftZIsTerminal.from _)
    (specULiftZIsTerminal.hom_ext _ _)).app <| .op <| .of <| Multiplicative M).hom

instance : IsMon_Hom ((diagSpecIso R M).inv.asOver (Spec R)) :=
  letI f := (algebraMap ℤ R).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom
  Mon_.instIsMon_HomHom
  ((specCommMonAlgPullback (CommRingCat.ofHom f) (specULiftZIsTerminal.from _)
    (specULiftZIsTerminal.hom_ext _ _)).app _).inv

/-- `Diag` is invariant under pullback. -/
def diagPullbackIso (f : T ⟶ S) : pullback f (Diag S M ↘ S) ≅ Diag T M :=
  pullbackSymmetry _ _ ≪≫ pullbackLeftPullbackSndIso _ _ _ ≪≫
    pullback.congrHom (by simp) (by simp)

@[reassoc (attr := simp)]
lemma diagPullbackIso_hom_over (f : T ⟶ S) :
    (diagPullbackIso f).hom ≫ Diag T M ↘ T = pullback.fst _ _ := by
  simp [diagPullbackIso, Diag.canonicallyOver_over]

@[reassoc (attr := simp)]
lemma diagPullbackIso_inv_fst (f : T ⟶ S) :
    (diagPullbackIso f).inv ≫ pullback.fst _ _ = Diag T M ↘ T := by
  simp [diagPullbackIso, Diag.canonicallyOver_over]

instance locallyOfFiniteType_diag [AddMonoid.FG M] : LocallyOfFiniteType (Diag S M ↘ S) := by
  apply MorphismProperty.pullback_snd
  simp only [specOverSpec_over, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType),
    CommRingCat.hom_ofHom, algebraMap_finiteType_iff_algebra_finiteType]
  infer_instance

@[simp] lemma locallyOfFiniteType_diag_iff [hS : Nonempty S] :
    LocallyOfFiniteType (Diag S M ↘ S) ↔ AddMonoid.FG M where
  mpr _ := inferInstance
  mp h := by
    wlog hS : ∃ R, S = Spec R
    · obtain ⟨x⟩ := ‹Nonempty S›
      obtain ⟨i, x, rfl⟩ := S.affineCover.exists_eq x
      have that : Nonempty (S.affineCover.obj i) := ⟨x⟩
      refine this (S := S.affineCover.obj i) ?_ ⟨_, rfl⟩
      have : LocallyOfFiniteType (pullback.fst (S.affineCover.map i) (S.Diag M ↘ S)) :=
        MorphismProperty.pullback_fst _ _ ‹_›
      rw [← diagPullbackIso_inv_fst (S.affineCover.map i)]
      infer_instance
    obtain ⟨R, rfl⟩ := hS
    rw [Spec_carrier, PrimeSpectrum.nonempty_iff_nontrivial] at hS
    replace h : LocallyOfFiniteType (Spec(R[M]) ↘ Spec R) := by
      rw [← MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType
        (diagSpecIso R M).hom]
      erw [comp_over]
      assumption
    simpa [specOverSpec_over, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType),
      algebraMap_finiteType_iff_algebra_finiteType, AddMonoidAlgebra.finiteType_iff_fg] using h

variable (S) in
def diagFunctor : AddCommGrpᵒᵖ ⥤ Grp_ (Over S) :=
  commGroupAddCommGroupEquivalence.inverse.op ⋙
    (commGrpAlg (ULift.{u} ℤ)).op ⋙ hopfSpec (.of <| ULift.{u} ℤ) ⋙
      (Over.pullback (specULiftZIsTerminal.from S)).mapGrp

@[simp] lemma diagFunctor_obj (M : AddCommGrpᵒᵖ) :
    (diagFunctor S).obj M = ⟨(Diag S M.unop).asOver S⟩ := rfl

@[simp] lemma diagFunctor_map {M N : AddCommGrpᵒᵖ} (f : M ⟶ N) :
    (diagFunctor S).map f = ⟨(Diag.map S f.unop.hom).asOver S⟩ := rfl

instance (M : AddCommMonCatᵒᵖ) : IsCommMon ((diagMonFunctor S).obj M).X :=
  inferInstanceAs (IsCommMon (asOver (Diag S M.unop) S))

instance (M : AddCommGrpᵒᵖ) : IsCommMon ((diagFunctor S).obj M).X :=
  inferInstanceAs (IsCommMon (asOver (Diag S M.unop) S))

@[simp]
lemma commHopfAlgCatEquivCogrpCommAlgCat_functor_map_ofHom_mul
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
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
    ((diagMonFunctorIso R).app M).hom.hom.left = (diagSpecIso R M.unop).hom := rfl

variable (R) in
def diagFunctorIso :
    diagFunctor (Spec R) ≅ commGroupAddCommGroupEquivalence.inverse.op ⋙
      (commGrpAlg R).op ⋙ hopfSpec R :=
  letI f := (algebraMap ℤ R).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom
  isoWhiskerLeft commGroupAddCommGroupEquivalence.inverse.op
    (specCommGrpAlgPullback (CommRingCat.ofHom f) (specULiftZIsTerminal.from _)
      (specULiftZIsTerminal.hom_ext _ _))

lemma diagFunctorIso_app (M : AddCommGrpᵒᵖ) :
    ((diagFunctorIso R).app M).hom.hom.left = (diagSpecIso R M.unop).hom := rfl

instance {R : Type*} [CommRing R] [IsDomain R] : (diagFunctor Spec(R)).Full :=
  have : (hopfSpec (CommRingCat.of R)).Full := hopfSpec.instFull
  .of_iso (diagFunctorIso (.of R)).symm

instance {R : Type*} [CommRing R] [IsDomain R] : (diagFunctor Spec(R)).Faithful :=
  have : (hopfSpec (CommRingCat.of R)).Faithful := hopfSpec.instFaithful
  .of_iso (diagFunctorIso (.of R)).symm

section

variable {G G' G'' H H' S : Scheme.{u}} [G.Over S] [G'.Over S] [G''.Over S] [H.Over S] [H'.Over S]
  [Grp_Class (G.asOver S)] [Grp_Class (G'.asOver S)] [Grp_Class (G''.asOver S)]
  [Grp_Class (H.asOver S)] [Grp_Class (H'.asOver S)]

variable (G G' S) in
def HomGrp : Type u := Additive (Grp_.mk (G.asOver S) ⟶ .mk (G'.asOver S))

instance [IsCommMon (G'.asOver S)] : AddCommGroup (HomGrp G G' S) := by
  delta HomGrp; infer_instance

def HomGrp.ofHom (f : G ⟶ G') [f.IsOver S] [IsMon_Hom (f.asOver S)] : HomGrp G G' S :=
  Additive.ofMul (Grp_.homMk (f.asOver S))

def HomGrp.hom (f : HomGrp G G' S) : G ⟶ G' := f.toMul.hom.left

@[simp]
lemma HomGrp.hom_ofHom (f : G ⟶ G') [f.IsOver S] [IsMon_Hom (f.asOver S)] :
  hom (ofHom (S := S) f) = f := rfl

@[ext]
lemma HomGrp.toHom_injective : Function.Injective (HomGrp.hom (G := G) (G' := G') (S := S)) := by
  intros _ _ H; delta HomGrp; ext; exact H

def HomGrp.comp (f : HomGrp G G' S) (g : HomGrp G' G'' S) : HomGrp G G'' S :=
  .ofMul (f.toMul ≫ g.toMul)

@[simp]
lemma HomGrp.hom_comp (f : HomGrp G G' S) (g : HomGrp G' G'' S) :
    (f.comp g).hom = f.hom ≫ g.hom := rfl

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

instance {X Y S : Scheme} [X.Over S] [Y.Over S] (e : X ≅ Y) [e.hom.IsOver S] : e.inv.IsOver S where
  comp_over := by rw [Iso.inv_comp_eq, comp_over]

instance {X Y S : Scheme} [X.Over S] [Y.Over S] [Mon_Class (X.asOver S)] [Mon_Class (Y.asOver S)]
    (e : X ≅ Y) [e.hom.IsOver S] [IsMon_Hom (e.hom.asOver S)] : IsMon_Hom (e.inv.asOver S) := by
  let e' : X.asOver S ≅ Y.asOver S := Over.isoMk e (by simp)
  have : IsMon_Hom e'.hom := ‹_›
  exact inferInstanceAs (IsMon_Hom e'.inv)

instance {X Y S : Scheme} [X.Over S] [Y.Over S] (e : X ≅ Y) [e.hom.IsOver S] :
    e.symm.hom.IsOver S where

instance {X Y S : Scheme} [X.Over S] [Y.Over S] [Mon_Class (X.asOver S)] [Mon_Class (Y.asOver S)]
    (e : X ≅ Y) [e.hom.IsOver S] [IsMon_Hom (e.hom.asOver S)] :
  IsMon_Hom (e.symm.hom.asOver S) where

instance {X S : Scheme.{u}} [X.Over S] : (Iso.refl X).hom.IsOver S where

instance {X S : Scheme.{u}} [X.Over S] [Mon_Class (X.asOver S)] :
    IsMon_Hom ((Iso.refl X).hom.asOver S) where

def HomGrp.congr (e₁ : G ≅ G') (e₂ : H ≅ H') [IsCommMon (H.asOver S)] [IsCommMon (H'.asOver S)]
    [e₁.hom.IsOver S] [IsMon_Hom (e₁.hom.asOver S)]
    [e₂.hom.IsOver S] [IsMon_Hom (e₂.hom.asOver S)] :
    HomGrp G H S ≃+ HomGrp G' H' S where
  toFun f := .comp (.comp (.ofHom e₁.inv) f) (.ofHom e₂.hom)
  invFun f := .comp (.comp (.ofHom e₁.hom) f) (.ofHom e₂.inv)
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f g := by simp [add_comp, comp_add]

end

variable (S) in
def diagHomGrp {M N : Type u} [AddCommGroup M] [AddCommGroup N] (f : M →+ N) :
    HomGrp (Diag S N) (Diag S M) S := .ofMul <| by
  have := (diagFunctor S).map (AddCommGrp.ofHom f).op
  dsimp at this
  exact this

lemma diagHomGrp_comp {M N O : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup O]
    (f : M →+ N) (g : N →+ O) :
    (diagHomGrp S g).comp (diagHomGrp S f) = diagHomGrp S (g.comp f) := by
  simpa [HomGrp, diagHomGrp, HomGrp.comp]
    using (S.diagFunctor.map_comp (AddCommGrp.ofHom g).op (AddCommGrp.ofHom f).op).symm

lemma diagHomGrp_add {M N : Type u} [AddCommGroup M] [AddCommGroup N] (f g : M →+ N) :
    diagHomGrp S (f + g) = diagHomGrp S f + diagHomGrp S g := by
  simpa [diagHomGrp] using congr(Additive.ofMul $(diagFunctor_map_add (S := S) f g))

def diagHomEquiv {R M N : Type u} [CommRing R] [IsDomain R] [AddCommGroup M] [AddCommGroup N] :
    (N →+ M) ≃+ HomGrp (Diag Spec(R) M) (Diag Spec(R) N) Spec(R) :=
  letI e := Functor.FullyFaithful.homEquiv (.ofFullyFaithful (diagFunctor Spec(R)))
    (X := .op (.of M)) (Y := .op (.of N))
  { toFun f := Additive.ofMul <| by have := e (AddCommGrp.ofHom f).op; dsimp at this; exact this
    invFun f := (e.symm <| by dsimp; exact f.toMul).unop.hom
    left_inv _ := by dsimp at *; erw [e.symm_apply_apply]; rfl
    right_inv _ := by dsimp at *; erw [e.apply_symm_apply]; rfl
    map_add' := diagHomGrp_add  }

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
    ∃ (A : Type u) (_ : AddCommGroup A) (e : G ≅ Diag S A) (_ : e.hom.IsOver S),
      IsMon_Hom <| e.hom.asOver S

instance {A : Type u} [AddCommGroup A] : IsDiagonalisable S (Diag S A) :=
  ⟨A, ‹_›, by exact .refl _, by dsimp; infer_instance, by dsimp; infer_instance⟩

lemma IsDiagonalisable.of_iso [IsDiagonalisable S H]
    (e : G ≅ H) [e.hom.IsOver S] [IsMon_Hom <| e.hom.asOver S] : IsDiagonalisable S G :=
  let ⟨A, _, e', _, _⟩ := ‹IsDiagonalisable S H›
  ⟨A, _, e.trans e', by dsimp; infer_instance, by dsimp; infer_instance⟩

lemma IsDiagonalisable.of_isIso [IsDiagonalisable S H]
    (f : G ⟶ H) [IsIso f] [f.IsOver S] [IsMon_Hom (f.asOver S)] : IsDiagonalisable S G :=
  have : IsMon_Hom (Hom.asOver (asIso f).hom S) := ‹_›
  .of_iso (asIso f)

end Scheme

section CommRing
variable {R : CommRingCat.{u}} {G : Scheme.{u}} [G.Over (Spec R)] [Grp_Class (asOver G (Spec R))]
  {A : Type u} [AddCommGroup A]

instance : IsDiagonalisable (Spec R) Spec(R[A]) := .of_isIso (diagSpecIso R A).inv

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
