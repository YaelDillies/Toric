/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Equiv
import Toric.GroupScheme.SchemeOver
import Toric.GroupScheme.SpecGrpAlg
import Toric.Hopf.GroupLike
import Toric.Hopf.HopfAlg
import Toric.Hopf.GrpAlg

open AlgebraicGeometry CategoryTheory Coalgebra Opposite

universe u

namespace HopfAlgebra

variable {A R : Type u} {B : Type*} [CommRing R] [CommGroup A] [Semiring B] [Bialgebra R B]

variable (R B) in
@[mk_iff]
class IsDiagonalisable : Prop where
  existsIso :
    ∃ (A : Type u) (_ : CommGroup A), Nonempty (B ≃ₐc[R] MonoidAlgebra R A)

instance : IsDiagonalisable R (MonoidAlgebra R A) :=
  ⟨⟨A, _, Nonempty.intro (BialgEquiv.refl _ _)⟩⟩
-- This causes universe errors unless we assume that `R` and `A` are in the same universe. Why?

lemma span_isGroupLikeElem_eq_top_of_isDiagonalizable : IsDiagonalisable R B ->
      Submodule.span R {a : B | IsGroupLikeElem R a} = ⊤ :=
  fun {existsIso := ⟨_, _, h⟩} ↦ MonoidAlgebra.groupLikeElem_span_of_iso (Classical.choice h).symm

end HopfAlgebra

section Field

namespace HopfAlgebra

variable {A K : Type u} {B : Type u} [Field K] [CommGroup A] [CommSemiring B] [Bialgebra K B]

-- also true over a commutative ring, but with a more complicated proof
lemma isDiagonalisable_of_span_isGroupLikeElem_eq_top :
    Submodule.span K {a : B | IsGroupLikeElem K a} = ⊤ → IsDiagonalisable K B := by
  intro h
  refine {existsIso := ⟨{a : B // IsGroupLikeElem K a}, inferInstance, ?_⟩}
  apply Nonempty.intro
  sorry

-- also true over a commutative ring, but with a more complicated proof
lemma isDiagonalisable_iff_span_isGroupLikeElem_eq_top :
    IsDiagonalisable K B ↔
      Submodule.span K {a : B | IsGroupLikeElem K a} = ⊤ :=
  ⟨span_isGroupLikeElem_eq_top_of_isDiagonalizable, isDiagonalisable_of_span_isGroupLikeElem_eq_top⟩

end HopfAlgebra

end Field




namespace AlgebraicGeometry.Scheme
section CommRing
variable {R : CommRingCat.{u}} {G : Over (Spec R)} [Grp_Class G] {A : Type u} [CommGroup A]

variable (G) in
@[mk_iff]
class IsDiagonalisable : Prop where
  existsIso :
    ∃ (A : Type u) (_ : CommGroup A),
      Nonempty <| Grp_.mk' G ≅
      ((specCommGrpAlgebra R).obj <| Opposite.op <| CommGrp.of A)

instance :
    IsDiagonalisable ((specCommGrpAlgebra R).obj <| Opposite.op <| CommGrp.of A).X :=
  ⟨⟨A, _, Nonempty.intro (Iso.refl _)⟩⟩

noncomputable instance : Algebra R (Γ.obj <| op G.left) := sorry

noncomputable instance : HopfAlgebra R (Γ.obj <| op G.left) := by
  have : Grp_Class (Opposite.op (CommAlg.of R (Γ.obj <| op G.left))) := sorry
  exact hopfAlgebra_unop (G := Opposite.op (CommAlg.of R (Γ.obj <| op G.left)))

end CommRing


section Field
variable {K : Type*} [Field K] {G : Over (Spec <| .of K)} [Grp_Class G]

noncomputable instance : HopfAlgebra K (Γ.obj <| op G.left) := by sorry
-- annoyingly, Lean is not able to use the instance on line 37; must find a way to fix this

-- This is false if we do not assume that `G` is affine.
/-- An algebraic group `G` over a field `K` is diagonalisable iff `Γ(G)` is `K`-spanned by its
group-like elements.

Note that this is more generally true over arbitrary commutative rings, but we do not prove that.
See SGA III, Exposé VIII for more info. -/
lemma isDiagonalisable_iff_span_isGroupLikeElem_eq_top :
    IsDiagonalisable G ↔
      Submodule.span K {a : Γ.obj <| op G.left | IsGroupLikeElem K a} = ⊤ := by
  refine ⟨fun {existsIso := ⟨A, _, h⟩} ↦ ?_, ?_⟩
  · set e : (Γ.obj <| op G.left) ≃ₐc[K] MonoidAlgebra K A := by
      set e := Classical.choice h
      sorry
  -- Here we need a "global sections" functor from R-group schemes to R-Hopf algebras.
    exact MonoidAlgebra.groupLikeElem_span_of_iso e.symm
  · sorry

end Field
end AlgebraicGeometry.Scheme
