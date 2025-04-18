/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Sophie Morel
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Toric.GroupScheme.HopfAffine
import Toric.Mathlib.AlgebraicGeometry.Pullbacks
import Toric.Mathlib.RingTheory.Bialgebra.GroupLike

noncomputable section

open AlgebraicGeometry CategoryTheory Bialgebra Opposite Limits

universe u v

namespace AlgebraicGeometry.Scheme
section Diag
variable {S : Scheme.{max u v}} {M G : Type v} [CommMonoid M] [CommGroup G]

variable (S M) in
/-- The spectrum of a monoid algebra over `ℤ`. -/
def Diag : Scheme.{max u v} :=
  pullback (Spec (.of (MonoidAlgebra (ULift.{max u v} ℤ) M)) ↘ Spec (.of <| ULift.{max u v} ℤ))
    (specULiftZIsTerminal.from S)

instance : (Diag S M).CanonicallyOver S := by unfold Diag; infer_instance
instance : Mon_Class (asOver (Diag S M) S) := by unfold Diag; infer_instance
instance : Grp_Class (asOver (Diag S G) S) := by unfold Diag; infer_instance

-- TODO: Fix. Either of the following ought to work:
-- instance : IsCommMon (asOver (Diag S M) S) := by unfold Diag; infer_instance
-- instance : IsCommMon (asOver (Diag S M) S) := isCommMon_asOver_pullback
#synth IsCommMon <| asOver (Spec (.of (MonoidAlgebra (ULift.{max u v} ℤ) M)))
  (Spec (.of <| ULift.{max u v} ℤ))

end Diag

section Scheme
variable {S G H : Scheme.{u}} [G.Over S] [H.Over S] [Grp_Class (asOver G S)]
  [Grp_Class (asOver H S)]

variable (S G) in
@[mk_iff]
class IsDiagonalisable : Prop where
  existsIso : ∃ (A : Type u) (_ : CommGroup A),
      Nonempty <| Grp_.mk' (asOver G S) ≅ .mk' (asOver (Diag S A) S)

lemma IsDiagonalisable.ofIso [IsDiagonalisable S H]
    (e : Grp_.mk' (asOver G S) ≅ .mk' (asOver H S)) : IsDiagonalisable S G :=
  let ⟨A, _, ⟨e'⟩⟩ := ‹IsDiagonalisable S H›; ⟨A, _, ⟨e.trans e'⟩⟩

end Scheme

section CommRing
variable {R : CommRingCat.{u}} {G : Scheme.{u}} [G.Over (Spec R)] [Grp_Class (asOver G (Spec R))]
  {A : Type u} [CommGroup A]

instance : IsDiagonalisable (Spec R) (Spec <| .of (MonoidAlgebra R A)) := sorry

-- FIXME: Lean is not able to use the instance on line 30
noncomputable instance : HopfAlgebra R (Γ.obj <| op G) := by sorry

variable [IsDomain R]

/-- An algebraic group `G` over a field `K` is diagonalisable iff it is affine and `Γ(G)` is
`K`-spanned by its group-like elements.

Note that this is more generally true over arbitrary commutative rings, but we do not prove that.
See SGA III, Exposé VIII for more info. -/
lemma isDiagonalisable_iff_span_isGroupLikeElem_eq_top :
    IsDiagonalisable (Spec R) G ↔ IsAffine G ∧
      Submodule.span R {a : Γ.obj <| op G | IsGroupLikeElem R a} = ⊤ := sorry

end CommRing
end AlgebraicGeometry.Scheme
