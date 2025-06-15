import Mathlib.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Lean Elab Term Meta Batteries.ExtendedBinder Parser.Term PrettyPrinter.Delaborator SubExpr

/-- `Spec(R)` is the spectrum of a commutative ring `R` as a scheme.

If `R`, `S` are commutative rings and `f : R →+* S`, then `Spec(f) : Spec(S) → Spec(R)`. -/
scoped syntax (name := specStx) "Spec("term")" : term

@[term_elab specStx]
def elabSpecStx : TermElab
  | `(Spec($x:term)), expectedType? => do
    logInfo m!"{expectedType?}"
    let isHom : MetaM Bool := do
      match expectedType? with
      | some expectedType =>
        match_expr expectedType with
        | Quiver.Hom _ _ => return true
        | _ => return false
      | none => return false
    let isHom : MetaM Bool := do
      match ← isHom with
      | true => return true
      | false =>
        let xElab ← elabTerm x none
    match ← isHom with
    | true => elabTerm (← `(Spec.map <| CommRingCat.ofHom $x)) expectedType?
    | false => elabTerm (← `(Spec <| .of $x)) expectedType?
  | _, _ => do throwUnsupportedSyntax

-- /-- The spectrum of a ring as a scheme. -/
-- scoped notation3 "Spec("R")" => Spec <| .of R
-- /-- A ring homomorphism as a map between spectra. -/
-- scoped notation3 "Spec("f")" => Spec.map <| CommRingCat.ofHom f

example {R : Type} [CommRing R] : Scheme := Spec(R)
example {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : Spec(S) ⟶ Spec(R) := Spec(f)

end AlgebraicGeometry
