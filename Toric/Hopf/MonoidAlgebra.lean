/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.Algebra.MonoidAlgebra.Defs
import Toric.Mathlib.RingTheory.Bialgebra.GroupLike
import Toric.Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Characterisation of group-like elements in group algebras

This file proves that the group-like elements of the group algebra `R[G]` over a domain `R` are
precisely the elements of the image of the inclusion `G → R[G]`.
-/

open Bialgebra Coalgebra Function

variable {R A G H I M N : Type*}

namespace MonoidAlgebra
section CommSemiring
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Group G] {x : MonoidAlgebra A G}

lemma isGroupLikeElem_of (g : G) : IsGroupLikeElem R (of A G g) where
  isUnit := .map _ <| Group.isUnit _
  comul_eq_tmul_self := by simp; rfl

@[simp]
lemma isGroupLikeElem_single_one (g : G) : IsGroupLikeElem R (single g 1 : MonoidAlgebra A G) :=
  isGroupLikeElem_of _

/-- A group algebra is spanned by its group-like elements. -/
@[simp]
lemma span_isGroupLikeElem : Submodule.span A {a : MonoidAlgebra A G | IsGroupLikeElem R a} = ⊤ :=
  eq_top_mono (Submodule.span_mono <| Set.range_subset_iff.2 isGroupLikeElem_of) <| by
    simp [← Finsupp.range_linearCombination]

end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

section Group
variable [Group G] [Group H]

open Submodule in
@[simp]
lemma isGroupLikeElem_iff_mem_range_of {x : MonoidAlgebra R G} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (of R G) where
  mp hx := by
    by_contra h
    have : LinearIndepOn R id (insert x <| .range (of R G)) :=
      linearIndepOn_isGroupLikeElem.mono <| by simp [Set.subset_def, hx]
    have : x.sum single ∉ span R (.range (of R G)) := by simpa using this.notMem_span_of_insert h
    refine this <| sum_mem fun g hg ↦ ?_
    rw [← mul_one (x g), ← smul_eq_mul, ← smul_single]
    refine smul_mem _ _ <| subset_span <| Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_of _

private noncomputable def mapDomainOfBialgHomFun (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) :
    G → H :=
  fun g ↦ (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose

@[simp]
private lemma single_mapDomainOfBialgHomFun_one (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H)
    (g : G) : single (mapDomainOfBialgHomFun f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose_spec

open Coalgebra in
/-- A bialgebra homomorphism `R[G] → R[H]` between group algebras over a domain `R` comes from a
group hom `G → H`.

See `MonoidAlgebra.mapDomainBialgHom` for the forward map. -/
noncomputable def mapDomainOfBialgHom (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) :
    G →* H where
  toFun := mapDomainOfBialgHomFun f
  map_one' := of_injective (k := R) <| by simp [← one_def]
  map_mul' g₁ g₂ := by
    refine of_injective (k := R) ?_
    simp only [of_apply, single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : R), ← single_mul_single, ← single_mul_single, map_mul]
    simp

protected lemma single_mapDomainOfBialgHom (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H)
    (g : G) (r : R) : single (mapDomainOfBialgHom f g) r = f (single g r) := by
  rw [← mul_one r, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul]
  exact congr(r • $(single_mapDomainOfBialgHomFun_one f g))

@[simp]
lemma mapDomainBialgHom_mapDomainOfBialgHom (f : MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) :
    mapDomainBialgHom R (mapDomainOfBialgHom f) = f :=
  BialgHom.coe_algHom_injective <| algHom_ext fun x ↦ by
    simpa [-single_mapDomainOfBialgHomFun_one] using single_mapDomainOfBialgHomFun_one f x

@[simp] lemma mapDomainOfBialgHom_mapDomainBialgHom (f : G →* H) :
    mapDomainOfBialgHom (mapDomainBialgHom (R := R) f) = f := by
  ext g; refine of_injective (k := R) ?_; simp [MonoidAlgebra.single_mapDomainOfBialgHom]

/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/
@[simps]
noncomputable def mapDomainBialgHomEquiv :
    (G →* H) ≃ (MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) where
  toFun := mapDomainBialgHom R
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

end Group

section CommGroup
variable [CommGroup G] [CommGroup H]

/-- The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group
algebras over a domain. -/
noncomputable def mapDomainBialgHomMulEquiv :
    (G →* H) ≃* (MonoidAlgebra R G →ₐc[R] MonoidAlgebra R H) where
  toEquiv := mapDomainBialgHomEquiv
  map_mul' f g := by simp

end CommGroup
end CommRing
end MonoidAlgebra


namespace AddMonoidAlgebra
section CommSemiring
variable [CommSemiring R] [Semiring A] [HopfAlgebra R A] [AddGroup G] {x : A[G]}

lemma isGroupLikeElem_of (g : G) : IsGroupLikeElem R (of A G g) where
  isUnit := .map _ <| Group.isUnit _
  comul_eq_tmul_self := by simp; rfl

@[simp]
lemma isGroupLikeElem_single (g : G) : IsGroupLikeElem R (single g 1 : A[G]) := isGroupLikeElem_of _

end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

section AddGroup
variable [AddGroup G] [AddGroup H] [AddGroup I]

open Submodule in
@[simp]
lemma isGroupLikeElem_iff_mem_range_of {x : R[G]} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (of R G) where
  mp hx := by
    by_contra h
    have : LinearIndepOn R id (insert x <| .range (of R G)) :=
      linearIndepOn_isGroupLikeElem.mono <| by simp [Set.subset_def, hx]
    have : x.sum single ∉ span R (.range (of R G)) := by simpa using this.notMem_span_of_insert h
    refine this <| sum_mem fun g hg ↦ ?_
    rw [← mul_one (x g), ← smul_eq_mul, ← smul_single]
    refine smul_mem _ _ <| subset_span <| Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_of _

private noncomputable def mapDomainOfBialgHomFun (f : R[G] →ₐc[R] R[H]) : G → H :=
  fun g ↦ (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose

@[simp]
private lemma single_mapDomainOfBialgHomFun_one (f : R[G] →ₐc[R] R[H]) (g : G) :
    single (mapDomainOfBialgHomFun f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose_spec

open Coalgebra in
/-- A bialgebra homomorphism `R[G] → R[H]` between group algebras over a domain `R` comes from a
group hom `G → H`.

See `AddMonoidAlgebra.mapDomainBialgHom` for the forward map. -/
noncomputable def mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) : G →+ H where
  toFun := mapDomainOfBialgHomFun f
  map_zero' := Multiplicative.ofAdd.injective <| of_injective (k := R) <| by simp [← one_def]
  map_add' g₁ g₂ := by
    refine Multiplicative.ofAdd.injective <| of_injective (k := R) ?_
    simp only [of_apply, single_mapDomainOfBialgHomFun_one, toAdd_ofAdd, ofAdd_add, toAdd_mul,
      single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : R), ← single_mul_single, ← single_mul_single, map_mul]
    simp

protected lemma single_mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) (g : G) (r : R) :
    single (mapDomainOfBialgHom f g) r = f (single g r) := by
  rw [← mul_one r, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul]
  exact congr(r • $(single_mapDomainOfBialgHomFun_one f g))

@[simp]
lemma mapDomainBialgHom_mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) :
    mapDomainBialgHom R (mapDomainOfBialgHom f) = f :=
  BialgHom.coe_algHom_injective <| algHom_ext fun x ↦ by
    simpa [-single_mapDomainOfBialgHomFun_one] using single_mapDomainOfBialgHomFun_one f x

@[simp] lemma mapDomainOfBialgHom_mapDomainBialgHom (f : G →+ H) :
    mapDomainOfBialgHom (mapDomainBialgHom R f) = f := by
  ext g
  refine Multiplicative.ofAdd.injective <| of_injective (k := R) ?_
  simp [AddMonoidAlgebra.single_mapDomainOfBialgHom]

@[simp] lemma mapDomainOfBialgHom_id : mapDomainOfBialgHom (.id R R[G]) = .id _ := by
  simp [← mapDomainBialgHom_id]

@[simp] lemma mapDomainOfBialgHom_comp (f : R[H] →ₐc[R] R[I]) (g : R[G] →ₐc[R] R[H]) :
    mapDomainOfBialgHom (f.comp g) = (mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g) := by
  rw [← mapDomainOfBialgHom_mapDomainBialgHom (R := R)
    ((mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g)),
    mapDomainBialgHom_comp, mapDomainBialgHom_mapDomainOfBialgHom,
    mapDomainBialgHom_mapDomainOfBialgHom]

/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/
@[simps]
noncomputable def mapDomainBialgHomEquiv : (G →+ H) ≃ (R[G] →ₐc[R] R[H]) where
  toFun := mapDomainBialgHom R
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

end AddGroup

section AddCommGroup
variable [AddCommGroup G] [AddCommGroup H]

/-- The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group
algebras over a domain. -/
noncomputable def mapDomainBialgHomAddEquiv : (G →+ H) ≃+ Additive (R[G] →ₐc[R] R[H]) where
  toEquiv := mapDomainBialgHomEquiv.trans Additive.ofMul
  map_add' f g := by simp

end AddCommGroup
end CommRing
end AddMonoidAlgebra

namespace MonoidAlgebra
variable (R A) [CommSemiring R] [Semiring A] [Bialgebra R A]

/-- The `R`-algebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[simps!]
noncomputable def liftGroupLikeAlgHom : MonoidAlgebra R (GroupLike R A) →ₐ[R] A :=
  lift R (GroupLike R A) A {
    toFun g := g.1
    map_one' := by simp
    map_mul' := by simp
  }

/-- The `R`-bialgebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[simps!]
noncomputable def liftGroupLikeBialgHom : MonoidAlgebra R (GroupLike R A) →ₐc[R] A := .ofAlgHom
  (liftGroupLikeAlgHom R A)
  (by ext ⟨x, hx⟩; simpa using hx.counit_eq_one)
  (by ext ⟨x, hx⟩; simpa using hx.comul_eq_tmul_self.symm)

end MonoidAlgebra
