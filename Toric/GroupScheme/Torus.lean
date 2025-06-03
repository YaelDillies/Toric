/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.FieldTheory.Separable
import Toric.GroupScheme.Diagonalizable
import Toric.MvLaurentPolynomial
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

/-!
# The standard algebraic torus

This file defines the standard algebraic torus over `Spec R` as `Spec (R ⊗ ℤ[Fₙ])`.
-/

noncomputable section

open CategoryTheory Opposite Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

universe u v

section IsSplitTorus
variable {S G H : Scheme.{u}} [G.Over S] [H.Over S] [Grp_Class (asOver G S)]
  [Grp_Class (asOver H S)]

variable (S G) in
@[mk_iff]
class IsSplitTorus : Prop where
  existsIso :
    ∃ (A : Type u) (_ : AddCommGroup A) (_ : Module.Free ℤ A),
      Nonempty <| Grp_.mk' (asOver G S) ≅ .mk' (asOver (Diag S A) S)

instance {A : Type u} [AddCommGroup A] [Module.Free ℤ A] : IsSplitTorus S (Diag S A) :=
  ⟨A, ‹_›, ‹_›, ⟨by exact .refl _⟩⟩

lemma IsSplitTorus.of_iso [IsSplitTorus S H]
    (e : Grp_.mk' (asOver G S) ≅ .mk' (asOver H S)) : IsSplitTorus S G :=
  let ⟨A, _, _, ⟨e'⟩⟩ := ‹IsSplitTorus S H›; ⟨A, _, ‹_›, ⟨e.trans e'⟩⟩

instance  (f : G ⟶ H) [IsIso f] [f.IsOver S] : IsIso (f.asOver S) :=
  have : IsIso ((Over.forget S).map (Hom.asOver f S)) := ‹_›
  isIso_of_reflects_iso _ (Over.forget _)

lemma IsSplitTorus.of_isIso [IsSplitTorus S H]
    (f : G ⟶ H) [IsIso f] [f.IsOver S] [IsMon_Hom (f.asOver S)] : IsSplitTorus S G :=
  have : IsMon_Hom (asIso (Hom.asOver f S)).hom := ‹_›
  .of_iso (H := H) ((Grp_.fullyFaithfulForget₂Mon_ _).preimageIso
    (Mon_.mkIso' (asIso (f.asOver S))))

lemma IsSplitTorus.of_isIso' [IsSplitTorus S G]
    (f : G ⟶ H) [IsIso f] [f.IsOver S] [IsMon_Hom (f.asOver S)] : IsSplitTorus S H :=
  have : IsMon_Hom (asIso (Hom.asOver f S)).hom := ‹_›
  .of_iso (H := G) ((Grp_.fullyFaithfulForget₂Mon_ _).preimageIso
    (.symm <| Mon_.mkIso' (asIso (f.asOver S))))

end IsSplitTorus

section IsTorus
variable {k : Type u} [Field k] {G H : Scheme.{u}} [G.Over (Spec (.of k))] [H.Over (Spec (.of k))]
  [Grp_Class (asOver G (Spec (.of k)))] [Grp_Class (asOver H (Spec (.of k)))]

variable (k G) in
@[mk_iff]
class IsTorus : Prop where
  existsSplit :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra.IsSeparable k L),
      IsSplitTorus (Spec (.of L)) <|
        pullback (G ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom <| algebraMap k L))

instance [IsSplitTorus (Spec (.of k)) G] : IsTorus k G :=
  ⟨⟨k, ‹_›, inferInstance, inferInstance, by
    simp only [Algebra.id.map_eq_id, CommRingCat.ofHom_id]
    rw [Spec.map_id]
    exact .of_isIso (pullback.fst (G ↘ (Spec (.of k))) (𝟙 (Spec (.of k))))⟩⟩

lemma IsTorus.of_iso [IsTorus k H]
    (e : Grp_.mk' (asOver G (Spec (.of k))) ≅ .mk' (asOver H (Spec (.of k)))) : IsTorus k G :=
  let ⟨L, _, _, _, hH⟩ := ‹IsTorus k H›; ⟨L, _, ‹_›, ‹_›,
    have e := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).mapGrp.mapIso e
    .of_iso (H := (pullback (H ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom <| algebraMap k L)))) (by convert e using 1)⟩

lemma IsTorus.of_isIso [IsTorus k H]
    (f : G ⟶ H) [IsIso f] [f.IsOver (Spec (.of k))] [IsMon_Hom (f.asOver (Spec (.of k)))] :
    IsTorus k G :=
  have : IsMon_Hom (asIso (Hom.asOver f (Spec (.of k)))).hom := ‹_›
  .of_iso (H := H) ((Grp_.fullyFaithfulForget₂Mon_ _).preimageIso
    (Mon_.mkIso' (asIso (f.asOver (Spec (.of k))))))

end IsTorus

section
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
    𝔾ₘ[Spec R, σ] ≅ Spec (.of <| MvLaurentPolynomial σ R) := diagSpecIso _ _

end

section Product
variable {S G H : Scheme.{u}} [G.Over S] [H.Over S] [Grp_Class (asOver G S)]
  [Grp_Class (asOver H S)]

@[simp]
lemma leftAsOver {X : Over S} : asOver X.left S = X := rfl

instance {X : Over S} [Grp_Class X] : Grp_Class <| asOver X.left S := by simpa

instance IsSplitTorus.product [IsSplitTorus S G] [IsSplitTorus S H] :
    IsSplitTorus S <| (asOver G S ⊗ asOver H S).left := sorry

end Product

end AlgebraicGeometry.Scheme
