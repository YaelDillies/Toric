/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.GroupScheme.SchemeOver
import Toric.Hopf.GroupLike

open AlgebraicGeometry CategoryTheory Coalgebra Opposite

universe u

section
variable {C A : Type*} [Category C] [ChosenFiniteProducts C]
    {R : CommRingCat} [CommGroup A]

instance :
    Grp_Class <| Over.mk <| Spec.map <| CommRingCat.ofHom <| algebraMap R <| MonoidAlgebra R A :=
  sorry

end

namespace AlgebraicGeometry.Scheme
section CommRing
variable {R : CommRingCat.{u}} {G : Over (Spec R)} [Grp_Class G]
    {A : Type u} [CommGroup A] [Monoid.FG A]

variable (G) in
@[mk_iff]
class IsDiagonalisable : Prop where
  existsIso :
    ∃ (A : Type u) (_ : CommGroup A) (_ : Monoid.FG A),
      Nonempty <| Grp_.mk' G ≅ sorry
      -- Grp_.mk' <| .mk <| Spec.map <| CommRingCat.ofHom <| algebraMap R <| MonoidAlgebra R A

instance :
    IsDiagonalisable <| .mk <| Spec.map <| CommRingCat.ofHom <| algebraMap R <| MonoidAlgebra R A :=
  ⟨⟨A, _, ‹_›, sorry⟩⟩

end CommRing

section Field
variable {K : Type*} [Field K] {G : Over (Spec <| .of K)} [Grp_Class G]

instance : HopfAlgebra K (Γ.obj <| op G.left) := sorry

/-- An algebraic group `G` over a field `K` is diagonalisable iff `Γ(G)` is `K`-spanned by its
group-like elements.

Note that this is more generally true over arbitrary commutative rings, but we do not prove that.
See SGA III, Exposé VIII for more info. -/
lemma isDiagonalisable_iff_span_isGroupLikeElem_eq_top :
    IsDiagonalisable G ↔
      Submodule.span K {a : Γ.obj <| op G.left | IsGroupLikeElem K a} = ⊤ := sorry

end Field
end AlgebraicGeometry.Scheme
