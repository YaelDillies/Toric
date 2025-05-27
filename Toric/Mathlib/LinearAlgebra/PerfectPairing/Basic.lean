import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Perfect pairings

This file defines perfect pairings of modules.

A perfect pairing of two (left) modules may be defined either as:
1. A bilinear map `M × N → R` such that the induced maps `M → Dual R N` and `N → Dual R M` are both
  bijective. It follows from this that both `M` and `N` are reflexive modules.
2. A linear equivalence `N ≃ Dual R M` for which `M` is reflexive. (It then follows that `N` is
  reflexive.)

In this file we provide a definition `IsPerfPair` corresponding to 1 above, together with logic
to connect 1 and 2.
-/

open Function Module

namespace LinearMap
variable {R K M N : Type*} [AddCommGroup M] [AddCommGroup N]

section CommRing
variable [CommRing R] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R} {x : M} {y : N}

/-- For a ring `R` and two modules `M` and `N`, a perfect pairing is a bilinear map `M × N → R`
that is bijective in both arguments. -/
@[ext]
class IsPerfPair (p : M →ₗ[R] N →ₗ[R] R) where
  bijective_left (p) : Bijective p
  bijective_right (p) : Bijective p.flip

/-- Given a perfect pairing between `M`and `N`, we may interchange the roles of `M` and `N`. -/
protected lemma IsPerfPair.flip (hp : p.IsPerfPair) : p.flip.IsPerfPair where
  bijective_left := IsPerfPair.bijective_right p
  bijective_right := IsPerfPair.bijective_left p

variable [p.IsPerfPair]

/-- Given a perfect pairing between `M`and `N`, we may interchange the roles of `M` and `N`. -/
instance flip.instIsPerfPair : p.flip.IsPerfPair := .flip ‹_›

variable (p)

/-- Turn a continuous perfect pairing between `M` and `N` into a map from `M` to continuous linear
maps `N → R`. -/
noncomputable def toPerfPair : M ≃ₗ[R] Dual R N :=
  .ofBijective { toFun := _, map_add' x y := by ext; simp, map_smul' r x := by ext; simp } <|
    IsPerfPair.bijective_left p

@[simp] lemma toLinearMap_toPerfPair (x : M) : p.toPerfPair x = p x := rfl
@[simp] lemma toPerfPair_apply (x : M) (y : N) : p.toPerfPair x y = p x y := rfl

@[simp] lemma apply_symm_toPerfPair_self (f : Dual R N) : p (p.toPerfPair.symm f) = f :=
  p.toPerfPair.apply_symm_apply f

@[simp] lemma apply_toPerfPair_flip (f : Dual R M) (x : M) : p x (p.flip.toPerfPair.symm f) = f x :=
  congr($(p.flip.apply_symm_toPerfPair_self ..) x)

include p in
lemma _root_.Module.IsReflexive.of_isPerfPair : IsReflexive R M where
  bijective_dual_eval' := by
    convert (p.toPerfPair.trans p.flip.toPerfPair.dualMap.symm).bijective
    ext x f
    simp

include p in
lemma _root_.Module.finrank_of_isPerfPair [Module.Finite R M] [Module.Free R M] :
    finrank R M = finrank R N :=
  ((Module.Free.chooseBasis R M).toDualEquiv.trans p.flip.toPerfPair.symm).finrank_eq

/-- A reflexive module has a perfect pairing with its dual. -/
protected instance IsPerfPair.id [IsReflexive R M] : IsPerfPair (.id (R := R) (M := Dual R M)) where
  bijective_left := bijective_id
  bijective_right := bijective_dual_eval R M

end CommRing

section Field
variable [Field K] [Module K M] [Module K N] {p : M →ₗ[K] N →ₗ[K] K} {x : M} {y : N}

/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear pairing. -/
lemma IsPerfPair.of_injective [FiniteDimensional K M] (h : Injective p) (h' : Injective p.flip) :
    p.IsPerfPair where
  bijective_left := ⟨h, by rwa [← p.flip_injective_iff₁]⟩
  bijective_right := ⟨h', by
    have : FiniteDimensional K N := FiniteDimensional.of_injective p.flip h'
    rwa [← p.flip.flip_injective_iff₁, LinearMap.flip_flip]⟩

/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear pairing. -/
lemma IsPerfPair.of_injective' [FiniteDimensional K N] (h : Injective p) (h' : Injective p.flip) :
    p.IsPerfPair := .flip <| .of_injective h' h

end Field
end LinearMap
