/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Hopf.GroupLike
import Toric.Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Toric.Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Characterisation of group-like elements in group algebras

This file proves that the group-like elements of the group algebra `k[G]` are precisely the elements
of the image of the inclusion `G → k[G]`.
-/

open Bialgebra Function

variable {K R A G H I : Type*}

namespace MonoidAlgebra
section CommSemiring
variable [CommSemiring R] [Semiring A] [HopfAlgebra R A] [Group G] {x : MonoidAlgebra A G}

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

/-- A bialgebra isomorphic to a group algebra is spanned by its group-like elements. -/
lemma span_isGroupLikeElem_of_iso {F H : Type*} [Semiring H] [Bialgebra R H]
    [EquivLike F (MonoidAlgebra R G) H] [BialgEquivClass F R (MonoidAlgebra R G) H] (f : F) :
    Submodule.span R {a : H | IsGroupLikeElem R a} = ⊤ := by
  rw [(Set.setOf_inj.mpr (funext (fun (a : H) ↦ propext_iff.mpr
    (isGroupLikeElem_map (a := a) (BialgEquivClass.toBialgEquiv f).symm)))).symm.trans
    (Equiv.setOf_apply_symm_eq_image_setOf (BialgEquivClass.toBialgEquiv f).toEquiv _),
    ← LinearEquiv.range (BialgEquivClass.toBialgEquiv f).toLinearEquiv, ← Submodule.map_top,
    ← span_isGroupLikeElem (R := R) (A := R) (G := G), Submodule.map_span]
  rfl

end CommSemiring

section Field
variable [Field K] [Group G]

section Group
variable [Group H]

open Submodule in
@[simp]
lemma isGroupLikeElem_iff_mem_range_of {x : MonoidAlgebra K G} :
    IsGroupLikeElem K x ↔ x ∈ Set.range (of K G) where
  mp hx := by
    by_contra h
    have : LinearIndepOn K id (insert x <| .range (of K G)) :=
      linearIndepOn_isGroupLikeElem.mono <| by simp [Set.subset_def, hx]
    rw [linearIndepOn_insert h, id_eq, Set.image_id, ← x.sum_single] at this
    refine this.2 <| sum_mem fun g hg ↦ ?_
    rw [← mul_one (x g), ← smul_eq_mul, ← smul_single]
    refine smul_mem _ _ <| subset_span <| Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_of _

private noncomputable def mapDomainOfBialgHomFun (f : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) :
    G → H :=
  fun g ↦ (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose

@[simp]
private lemma single_mapDomainOfBialgHomFun_one (f : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H)
    (g : G) : single (mapDomainOfBialgHomFun f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose_spec

open Coalgebra in
/-- A bialgebra homomorphism `K[G] → K[H]` between group algebras over a field `K` comes from a
group hom `G → H`. This is that group hom, namely the inverse of `MonoidAlgebra.mapDomainBialgHom`.
-/
noncomputable
def mapDomainOfBialgHom (f : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) : G →* H where
  toFun := mapDomainOfBialgHomFun f
  map_one' := of_injective (k := K) <| by simp [← one_def]
  map_mul' g₁ g₂ := by
    refine of_injective (k := K) ?_
    simp only [of_apply, single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : K), ← single_mul_single, ← single_mul_single, map_mul]
    simp

protected lemma single_mapDomainOfBialgHom (f : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H)
    (g : G) (k : K) : single (mapDomainOfBialgHom f g) k = f (single g k) := by
  rw [← mul_one k, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul]
  exact congr(k • $(single_mapDomainOfBialgHomFun_one f g))

@[simp]
lemma mapDomainBialgHom_mapDomainOfBialgHom (f : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) :
    mapDomainBialgHom K (mapDomainOfBialgHom f) = f :=
  BialgHom.coe_algHom_injective <| algHom_ext fun x ↦ by
    simpa [-single_mapDomainOfBialgHomFun_one] using single_mapDomainOfBialgHomFun_one f x

@[simp] lemma mapDomainOfBialgHom_mapDomainBialgHom (f : G →* H) :
    mapDomainOfBialgHom (mapDomainBialgHom (R := K) f) = f := by
  ext g; refine of_injective (k := K) ?_; simp [MonoidAlgebra.single_mapDomainOfBialgHom]

/-- The equivalence between group homs `G → H` and bialgebra homs `K[G] → K[H]` of group algebras
over a field. -/
noncomputable def mapDomainBialgHomEquiv :
    (G →* H) ≃ (MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) where
  toFun := mapDomainBialgHom K
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

end Group

section CommGroup
variable [CommGroup H]

-- TODO(Yaël): Fix diamond with multiplication as composition
noncomputable
instance : CommGroup <| MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H :=
  mapDomainBialgHomEquiv.symm.commGroup

/-- The group isomorphism between group homs `G → H` and bialgebra homs `K[G] → K[H]` of group
algebras over a field. -/
noncomputable def mapDomainBialgHomMulEquiv :
    (G →* H) ≃* (MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) :=
  mapDomainBialgHomEquiv.symm.mulEquiv.symm

end CommGroup
end Field
end MonoidAlgebra


namespace AddMonoidAlgebra
section CommSemiring
variable [CommSemiring R] [Semiring A] [HopfAlgebra R A] [AddGroup G] {x : A[G]}

lemma isGroupLikeElem_of (g : G) : IsGroupLikeElem R (of A G g) where
  isUnit := .map _ <| Group.isUnit _
  comul_eq_tmul_self := by simp; rfl

@[simp]
lemma isGroupLikeElem_single (g : G) : IsGroupLikeElem R (single g 1 : A[G]) :=
  isGroupLikeElem_of _

end CommSemiring

section Field
variable [Field K] [AddGroup G]

section AddGroup
variable [AddGroup H] [AddGroup I]

open Submodule in
@[simp]
lemma isGroupLikeElem_iff_mem_range_of {x : K[G]} :
    IsGroupLikeElem K x ↔ x ∈ Set.range (of K G) where
  mp hx := by
    by_contra h
    have : LinearIndepOn K id (insert x <| .range (of K G)) :=
      linearIndepOn_isGroupLikeElem.mono <| by simp [Set.subset_def, hx]
    rw [linearIndepOn_insert h, id_eq, Set.image_id, ← x.sum_single] at this
    refine this.2 <| sum_mem fun g hg ↦ ?_
    rw [← mul_one (x g), ← smul_eq_mul, ← smul_single]
    refine smul_mem _ _ <| subset_span <| Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_of _

private noncomputable def mapDomainOfBialgHomFun (f : K[G] →ₐc[K] K[H]) : G → H :=
  fun g ↦ (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose

@[simp]
private lemma single_mapDomainOfBialgHomFun_one (f : K[G] →ₐc[K] K[H]) (g : G) :
    single (mapDomainOfBialgHomFun f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose_spec

open Coalgebra in
/-- A bialgebra homomorphism `K[G] → K[H]` between group algebras over a field `K` comes from a
group hom `G → H`. This is that group hom, namely the inverse of
`AddMonoidAlgebra.mapDomainBialgHom`. -/
noncomputable def mapDomainOfBialgHom (f : K[G] →ₐc[K] K[H]) : G →+ H where
  toFun := mapDomainOfBialgHomFun f
  map_zero' := Multiplicative.ofAdd.injective <| of_injective (k := K) <| by simp [← one_def]
  map_add' g₁ g₂ := by
    refine Multiplicative.ofAdd.injective <| of_injective (k := K) ?_
    simp only [of_apply, single_mapDomainOfBialgHomFun_one, toAdd_ofAdd, ofAdd_add, toAdd_mul,
      single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : K), ← single_mul_single, ← single_mul_single, map_mul]
    simp

protected lemma single_mapDomainOfBialgHom (f : K[G] →ₐc[K] K[H])
    (g : G) (k : K) : single (mapDomainOfBialgHom f g) k = f (single g k) := by
  rw [← mul_one k, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul]
  exact congr(k • $(single_mapDomainOfBialgHomFun_one f g))

@[simp]
lemma mapDomainBialgHom_mapDomainOfBialgHom (f : K[G] →ₐc[K] K[H]) :
    mapDomainBialgHom K (mapDomainOfBialgHom f) = f :=
  BialgHom.coe_algHom_injective <| algHom_ext fun x ↦ by
    simpa [-single_mapDomainOfBialgHomFun_one] using single_mapDomainOfBialgHomFun_one f x

@[simp] lemma mapDomainOfBialgHom_mapDomainBialgHom (f : G →+ H) :
    mapDomainOfBialgHom (mapDomainBialgHom K f) = f := by
  ext g
  refine Multiplicative.ofAdd.injective <| of_injective (k := K) ?_
  simp [AddMonoidAlgebra.single_mapDomainOfBialgHom]

@[simp] lemma mapDomainOfBialgHom_id : mapDomainOfBialgHom (.id K K[G]) = .id _ := by
  simp [← mapDomainBialgHom_id]

@[simp] lemma mapDomainOfBialgHom_comp (f : K[H] →ₐc[K] K[I]) (g : K[G] →ₐc[K] K[H]) :
    mapDomainOfBialgHom (f.comp g) = (mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g) := by
  rw [← mapDomainOfBialgHom_mapDomainBialgHom (K := K)
    ((mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g)),
    mapDomainBialgHom_comp, mapDomainBialgHom_mapDomainOfBialgHom,
    mapDomainBialgHom_mapDomainOfBialgHom]

/-- The equivalence between group homs `G → H` and bialgebra homs `K[G] → K[H]` of group algebras
over a field. -/
noncomputable def mapDomainBialgHomEquiv :
    (G →+ H) ≃ (K[G] →ₐc[K] K[H]) where
  toFun := mapDomainBialgHom K
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

end AddGroup

section AddCommGroup
variable [AddCommGroup H]

-- TODO(Yaël): Fix diamond with multiplication as composition
noncomputable
instance : AddCommGroup <| K[G] →ₐc[K] K[H] := mapDomainBialgHomEquiv.symm.addCommGroup

/-- The group isomorphism between group homs `G → H` and bialgebra homs `K[G] → K[H]` of group
algebras over a field. -/
noncomputable def mapDomainBialgHomMulEquiv : (G →+ H) ≃+ (K[G] →ₐc[K] K[H]) :=
  mapDomainBialgHomEquiv.symm.addEquiv.symm

end AddCommGroup
end Field
end AddMonoidAlgebra

namespace MonoidAlgebra

open Bialgebra Coalgebra

variable (R A : Type*)

variable [CommSemiring R] [Semiring A] [Bialgebra R A]

/-- The `R`-algebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[simps!]
noncomputable def liftGroupLikeAlgHom : MonoidAlgebra R (GroupLike R A) →ₐ[R] A :=
  MonoidAlgebra.lift R (GroupLike R A) A {
    toFun g := g.1
    map_one' := by simp
    map_mul' := by simp
  }

/-- The `R`-bialgebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[simps!]
noncomputable def liftGroupLikeBialgHom (hinj : Injective (algebraMap R A)) :
    MonoidAlgebra R (GroupLike R A) →ₐc[R] A where
  __ := liftGroupLikeAlgHom R A
  map_smul' a x := show (liftGroupLikeAlgHom R A) (a • x) = _ by simp
  counit_comp := by ext ⟨x, hx⟩; simpa using hx.counit_eq_one hinj
  map_comp_comul := by ext ⟨x, hx⟩; simpa using hx.comul_eq_tmul_self.symm

end MonoidAlgebra
