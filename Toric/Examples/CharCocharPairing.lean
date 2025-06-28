/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Toric.GroupScheme.Character
import Toric.Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Toric.Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Demo of the perfect pairing between characters and cocharacters of a torus

In this file, we present the pairing between characters and cocharacters and .

## TODO

Actually compute the pairing on an explicit torus to be the usual inner product on `ℤⁿ`.
-/

noncomputable section

open AlgebraicGeometry Scheme

/-!
Let `S` be a scheme and `G` be a group scheme over `S`.

We denote the characters of `G` by `X(S, G)` and the cocharacters by `X*(S, G)`.
-/

example {S G : Scheme} [G.Over S] [Grp_Class (G.asOver S)] : Type := X(S, G)
example {S G : Scheme} [G.Over S] [Grp_Class (G.asOver S)] : Type := X*(S, G)

/-!
Let `R` be a domain and `G` be a split torus over `R`.

Then we have a pairing between `X(Spec R, G)` and `X*(Spec R, G)`.

If furthermore `G := 𝔾ₘ[Spec R, σ]` is the explicit torus with finite dimensions given by `σ`,
then this pairing is perfect.
-/

example {R : CommRingCat.{0}} [IsDomain R] {G : Scheme} [G.Over (Spec R)]
    [CommGrp_Class (G.asOver (Spec R))] :
    X*(Spec R, G) →ₗ[ℤ] X(Spec R, G) →ₗ[ℤ] ℤ := charPairing R G

example {R : CommRingCat} [IsDomain R] {σ : Type} [Finite σ] :
    (charPairing R 𝔾ₘ[Spec R, σ]).IsPerfPair := isPerfPair_charPairing
