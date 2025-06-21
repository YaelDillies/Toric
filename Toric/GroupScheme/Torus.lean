/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.FieldTheory.Separable
import Toric.GroupScheme.Diagonalizable
import Toric.Mathlib.CategoryTheory.Comma.Over.OverClass
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Ring.Adjunctions
import Toric.MvLaurentPolynomial

/-!
# The standard algebraic torus

This file defines the standard algebraic torus over `Spec R` as `Spec (R ⊗ ℤ[Fₙ])`.
-/

noncomputable section

open CategoryTheory Opposite Limits
open scoped AddMonoidAlgebra

universe u

namespace AlgebraicGeometry.Scheme
section IsSplitTorusOver
variable {G H S : Scheme.{u}} [G.Over S] [H.Over S] [Grp_Class (asOver G S)]
  [Grp_Class (asOver H S)]

variable (G S) in
@[mk_iff]
class IsSplitTorusOver : Prop where
  existsIso :
    ∃ (A : Type u) (_ : AddCommGroup A) (_ : Module.Free ℤ A) (e : G ≅ Diag S A)
      (_ : e.hom.IsOver S), IsMon_Hom (e.hom.asOver S)

instance diag_isSplitTorusOver {A : Type u} [AddCommGroup A] [Module.Free ℤ A] :
    (Diag S A).IsSplitTorusOver S :=
  ⟨A, ‹_›, ‹_›, by exact .refl (S.Diag A), by dsimp; infer_instance, by dsimp; infer_instance⟩

lemma IsSplitTorusOver.of_isIso [H.IsSplitTorusOver S] (f : G ⟶ H) [IsIso f] [f.IsOver S]
    [IsMon_Hom (f.asOver S)] : G.IsSplitTorusOver S :=
  have : IsMon_Hom ((asIso f).hom.asOver S) := ‹_›
  let ⟨A, _, _, e, _, _⟩ := ‹H.IsSplitTorusOver S›
  ⟨A, _, ‹_›, (asIso f).trans e, by dsimp; infer_instance, by dsimp; infer_instance⟩

lemma IsSplitTorusOver.of_isIso' [G.IsSplitTorusOver S]
    (f : G ⟶ H) [IsIso f] [f.IsOver S] [IsMon_Hom (f.asOver S)] : H.IsSplitTorusOver S :=
  have : IsMon_Hom ((inv f).asOver S) := by
    simpa using inferInstanceAs <| IsMon_Hom (asIso <| f.asOver S).inv
  .of_isIso (inv f)

lemma IsSplitTorusOver.of_iso [H.IsSplitTorusOver S] (e : G ≅ H) [e.hom.IsOver S]
    [IsMon_Hom (e.hom.asOver S)] : G.IsSplitTorusOver S := of_isIso e.hom

variable (G S) in
/-- Every split torus that's locally of finite type is isomorphic to `𝔾ₘⁿ` for some `n`. -/
lemma exists_iso_diag_finite_of_isSplitTorusOver_locallyOfFiniteType [G.IsSplitTorusOver S]
    [hG : LocallyOfFiniteType (G ↘ S)] [Nonempty S] :
    ∃ (ι : Type u) (_ : Finite ι) (e : G ≅ Diag S ℤ[ι]) (_ : e.hom.IsOver S),
      IsMon_Hom (e.hom.asOver S) := by
  obtain ⟨A, _, _, e, _, _⟩ := ‹G.IsSplitTorusOver S›
  replace hG : LocallyOfFiniteType (Diag S A ↘ S) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType e.hom]
    erw [comp_over e.hom]
    assumption
  rw [locallyOfFiniteType_diag_iff] at hG
  exact ⟨Module.Free.ChooseBasisIndex ℤ A, inferInstance,
    e.trans <| Diag.mapIso S (Module.Free.chooseBasis ℤ A).repr.toAddEquiv,
    by dsimp; infer_instance, by dsimp; infer_instance⟩

end IsSplitTorusOver

section IsTorusOver
variable {k : Type u} [Field k] {G H : Scheme.{u}} [G.Over Spec(k)] [H.Over Spec(k)]
  [Grp_Class (G.asOver Spec(k))] [Grp_Class (H.asOver Spec(k))]

variable (k G) in
@[mk_iff]
class IsTorusOver : Prop where
  existsSplit :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra.IsSeparable k L),
      (pullback (G ↘ Spec(k)) <| Spec.map <| CommRingCat.ofHom <|
        algebraMap k L).IsSplitTorusOver Spec(L)

instance [G.IsSplitTorusOver Spec(k)] : G.IsTorusOver k := by
  refine ⟨k, ‹_›, inferInstance, inferInstance, ?_⟩
  simp only [Algebra.id.map_eq_id, CommRingCat.ofHom_id]
  suffices (pullback (G ↘ Spec(k)) (𝟙 _)).IsSplitTorusOver Spec(k) by
    convert this <;> simp
  exact .of_isIso (pullback.fst (G ↘ Spec(k)) (𝟙 _))

lemma IsTorusOver.of_iso (e : G ≅ H) [e.hom.IsOver Spec(k)] [IsMon_Hom (e.hom.asOver Spec(k))]
    [H.IsTorusOver k] : G.IsTorusOver k := by
  obtain ⟨L, _, _, _, hH⟩ := ‹H.IsTorusOver k›
  refine ⟨L, _, ‹_›, ‹_›, ?_⟩
  let e'' := (Over.pullback <| Spec.map <| CommRingCat.ofHom <| algebraMap k L).mapGrp.mapIso <|
    Grp_.mkIso (M := .mk <| G.asOver Spec(k)) (N := .mk <| H.asOver Spec(k)) (Over.isoMk e)
      (IsMon_Hom.one_hom (e.hom.asOver Spec(k))) (IsMon_Hom.mul_hom (e.hom.asOver Spec(k)))
  let e' := (Grp_.forget _ ⋙ Over.forget _).mapIso e''
  dsimp at e'
  have : e'.hom.IsOver Spec(L) := by simp [e', e'']
  have : IsMon_Hom <| e'.hom.asOver Spec(L) := Mon_.instIsMon_HomHom e''.hom
  exact .of_iso e'

lemma IsTorusOver.of_isIso [H.IsTorusOver k]
    (f : G ⟶ H) [IsIso f] [f.IsOver Spec(k)] [IsMon_Hom (f.asOver Spec(k))] :
    G.IsTorusOver k :=
  have : IsMon_Hom (Hom.asOver (asIso f).hom Spec(k)) := ‹_›
  .of_iso (asIso f)

end IsTorusOver

/-- The (split) algebraic torus over `S` indexed by `σ`. -/
abbrev SplitTorus (S : Scheme) (σ : Type u) : Scheme.{u} := Diag S <| FreeAbelianGroup σ

@[inherit_doc SplitTorus]
notation3 "𝔾ₘ[" S ", " σ "]" => SplitTorus S σ

/-- The multiplicative group over `S`. -/
notation3 "𝔾ₘ["S"]" => 𝔾ₘ[S, PUnit]

-- attribute [ext] Comma

-- def SplitTorus.representableBy (S : Scheme) (σ : Type*) :
--     ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
--       CommGrp.coyonedaRight.obj (op σ) ⋙ CategoryTheory.forget _).RepresentableBy
--       (𝔾ₘ[S, σ].asOver S) := by
--   letI X :=
--   (((((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).comp
--     (Over.equivalenceOfIsTerminal specULiftZIsTerminal).toAdjunction).comp <|
--     (ΓSpec.adjunction.comp <| (CommRingCat.forget₂Adj CommRingCat.isInitial).op.comp <|
--       CommGrp.forget₂CommMonAdj.op.comp <|
--         commGroupAddCommGroupEquivalence.symm.toAdjunction.op.comp <|
--           AddCommGrp.adj.op)).representableBy (op σ)).ofIso <|
--     isoWhiskerRight (NatIso.op (Over.forgetMapTerminal _ _))
--       (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
--         CommMonCat.units ⋙ CategoryTheory.forget _ ⋙ opOp _ ⋙ yoneda.obj (op σ)) ≪≫
--         (isoWhiskerLeft ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
--           CommMonCat.units ⋙ CategoryTheory.forget CommGrp) (Coyoneda.opIso.app _)))
--   convert X using 1
--   apply Comma.ext
--   · dsimp [SplitTorus, Diag]
--     congr 1


variable {R : CommRingCat} {σ : Type*}

variable (R σ) in
/-- The split torus with dimensions `σ` over `Spec R` is isomorphic to `Spec R[ℤ^σ]`. -/
abbrev splitTorusIso (R : CommRingCat) (σ : Type*) :
    𝔾ₘ[Spec R, σ] ≅ Spec(MvLaurentPolynomial σ R) := diagSpecIso _ _

end AlgebraicGeometry.Scheme
