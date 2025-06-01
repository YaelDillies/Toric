/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Sophie Morel
-/
import Toric.GroupScheme.SpecGrpAlg

open AlgebraicGeometry CategoryTheory Bialgebra Opposite
open scoped AddMonoidAlgebra

universe u

namespace AlgebraicGeometry.Scheme
section CommRing
variable {R : CommRingCat.{u}} {G : Scheme.{u}} [G.Over (Spec R)] [Grp_Class (G.asOver (Spec R))]
  {A : Type u} [AddCommGroup A]

variable (R G) in
@[mk_iff]
class IsDiagonalisable : Prop where
  existsIso :
    ∃ (A : Type u) (_ : AddCommGroup A),
      Nonempty <| .mk' (G.asOver (Spec R)) ≅ (specCommGrpAlg R).obj (.op <| .of <| Multiplicative A)

instance : IsDiagonalisable R (Spec <| .of R[A]) := ⟨⟨A, _, ⟨.refl _⟩⟩⟩

variable [IsDomain R]

/-- An affine algebraic group `G` over a domain `R` is diagonalisable iff it is affine and `Γ(G)` is
`R`-spanned by its group-like elements.

Note that this is more generally true over arbitrary commutative rings, but we do not prove that.
See SGA III, Exposé VIII for more info.

Note that more generally a not necessarily affine algebraic group `G` over a field `K` is
diagonalisable iff it is affine and `Γ(G)` is `K`-spanned by its group-like elements, but we do not
prove that. -/
lemma isDiagonalisable_iff_span_isGroupLikeElem_eq_top [IsAffine G] :
    IsDiagonalisable R G ↔ Submodule.span R {a : Γ(G, ⊤) | IsGroupLikeElem R a} = ⊤ :=
  sorry

end CommRing
end AlgebraicGeometry.Scheme
