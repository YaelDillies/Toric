/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Sophie Morel
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.Separable
import Toric.GroupScheme.MonoidAlgebra

open AlgebraicGeometry CategoryTheory Bialgebra Opposite Limits
open scoped AddMonoidAlgebra

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
