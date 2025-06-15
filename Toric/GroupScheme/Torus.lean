/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.FieldTheory.Separable
import Toric.GroupScheme.Diagonalizable
import Toric.MvLaurentPolynomial

/-!
# The standard algebraic torus

This file defines the standard algebraic torus over `Spec R` as `Spec (R ⊗ ℤ[Fₙ])`.
-/

noncomputable section

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme

universe u v

section IsSplitTorusOver
variable {G H S : Scheme.{u}} [G.Over S] [H.Over S] [Grp_Class (asOver G S)]
  [Grp_Class (asOver H S)]

variable (G S) in
@[mk_iff]
class IsSplitTorusOver : Prop where
  existsIso :
    ∃ (A : Type u) (_ : AddCommGroup A) (_ : Module.Free ℤ A),
      Nonempty <| Grp_.mk' (asOver G S) ≅ .mk' (asOver (Diag S A) S)

instance {A : Type u} [AddCommGroup A] [Module.Free ℤ A] : (Diag S A).IsSplitTorusOver S :=
  ⟨A, ‹_›, ‹_›, ⟨by exact .refl _⟩⟩

lemma IsSplitTorusOver.of_iso [H.IsSplitTorusOver S]
    (e : Grp_.mk' (asOver G S) ≅ .mk' (asOver H S)) : G.IsSplitTorusOver S :=
  let ⟨A, _, _, ⟨e'⟩⟩ := ‹H.IsSplitTorusOver S›; ⟨A, _, ‹_›, ⟨e.trans e'⟩⟩

instance  (f : G ⟶ H) [IsIso f] [f.IsOver S] : IsIso (f.asOver S) :=
  have : IsIso ((Over.forget S).map (Hom.asOver f S)) := ‹_›
  isIso_of_reflects_iso _ (Over.forget _)

lemma IsSplitTorusOver.of_isIso [H.IsSplitTorusOver S]
    (f : G ⟶ H) [IsIso f] [f.IsOver S] [IsMon_Hom (f.asOver S)] : G.IsSplitTorusOver S :=
  have : IsMon_Hom (asIso (Hom.asOver f S)).hom := ‹_›
  .of_iso (H := H) ((Grp_.fullyFaithfulForget₂Mon_ _).preimageIso
    (Mon_.mkIso' (asIso (f.asOver S))))

lemma IsSplitTorusOver.of_isIso' [G.IsSplitTorusOver S]
    (f : G ⟶ H) [IsIso f] [f.IsOver S] [IsMon_Hom (f.asOver S)] : H.IsSplitTorusOver S :=
  have : IsMon_Hom (asIso (Hom.asOver f S)).hom := ‹_›
  .of_iso (H := G) ((Grp_.fullyFaithfulForget₂Mon_ _).preimageIso
    (.symm <| Mon_.mkIso' (asIso (f.asOver S))))

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

instance [G.IsSplitTorusOver Spec(k)] : G.IsTorusOver k :=
  ⟨⟨k, ‹_›, inferInstance, inferInstance, by
    simp only [Algebra.id.map_eq_id, CommRingCat.ofHom_id]
    suffices (pullback (G ↘ Spec(k)) (𝟙 _)).IsSplitTorusOver Spec(k) by
      convert this <;> simp
    exact .of_isIso (pullback.fst (G ↘ Spec(k)) (𝟙 _))⟩⟩

lemma IsTorusOver.of_iso [H.IsTorusOver k]
    (e : Grp_.mk' (asOver G Spec(k)) ≅ .mk' (asOver H Spec(k))) : G.IsTorusOver k  :=
  let ⟨L, _, _, _, hH⟩ := ‹H.IsTorusOver k›; ⟨L, _, ‹_›, ‹_›,
    have e := (Over.pullback Spec(algebraMap k L)).mapGrp.mapIso e
    .of_iso (H := pullback (H ↘ Spec(k)) Spec(algebraMap k L)) (by convert e using 1)⟩

lemma IsTorusOver.of_isIso [H.IsTorusOver k]
    (f : G ⟶ H) [IsIso f] [f.IsOver Spec(k)] [IsMon_Hom (f.asOver Spec(k))] :
    G.IsTorusOver k  :=
  have : IsMon_Hom (asIso (Hom.asOver f Spec(k))).hom := ‹_›
  .of_iso (H := H) ((Grp_.fullyFaithfulForget₂Mon_ _).preimageIso
    (Mon_.mkIso' (asIso (f.asOver Spec(k)))))

end IsTorusOver

/-- The (split) algebraic torus over `S` indexed by `σ`. -/
abbrev SplitTorus (S : Scheme) (σ : Type u) : Scheme.{u} := Diag S <| FreeAbelianGroup σ

@[inherit_doc SplitTorus]
notation3 "𝔾ₘ[" S ", " σ "]" => SplitTorus S σ

/-- The multiplicative group over `S`. -/
notation3 "𝔾ₘ["S"]" => 𝔾ₘ[S, PUnit]

-- def SplitTorus.representableBy (S : Scheme) (σ : Type*) :
--     ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
--       CommGrp.coyonedaRight.obj (op σ) ⋙ forget _).RepresentableBy
--       (𝔾ₘ[S, σ].asOver S) :=
--   ((((Over.mapPullbackAdj (terminal.from S)).comp
--     (Over.equivalenceOfIsTerminal terminalIsTerminal).toAdjunction).comp <|
--     (ΓSpec.adjunction.comp <| (CommRingCat.forget₂Adj CommRingCat.isInitial).op.comp <|
--       CommGrp.forget₂CommMonAdj.op.comp <|
--         commGroupAddCommGroupEquivalence.symm.toAdjunction.op.comp <|
--           AddCommGrp.adj.op)).representableBy (op σ)).ofIso <|
--     isoWhiskerRight (NatIso.op (Over.forgetMapTerminal _ _))
--       (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
--         CommMonCat.units ⋙ forget _ ⋙ opOp _ ⋙ yoneda.obj (op σ)) ≪≫
--         (isoWhiskerLeft ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
--           CommMonCat.units ⋙ forget CommGrp) (Coyoneda.opIso.app _))

variable {R : CommRingCat} {σ : Type*}

variable (R σ) in
/-- The split torus with dimensions `σ` over `Spec R` is isomorphic to `Spec R[ℤ^σ]`. -/
abbrev splitTorusIso (R : CommRingCat) (σ : Type*) :
    𝔾ₘ[Spec R, σ] ≅ Spec(MvLaurentPolynomial σ R) := diagSpecIso _ _

end AlgebraicGeometry.Scheme
