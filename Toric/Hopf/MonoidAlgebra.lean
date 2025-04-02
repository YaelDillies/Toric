
/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Toric.Hopf.GroupLike

/-!
# Characterisation of group-like elements in group algebras

This file proves that the group-like elements of the group algebra `k[G]` are precisely the elements
of the image of the inclusion `G → k[G]`.
-/

open Coalgebra

namespace MonoidAlgebra
variable {K R A G H : Type*}

section CommSemiring
variable [CommSemiring R] [Semiring A] [HopfAlgebra R A] [Group G]
  {x : MonoidAlgebra A G}

lemma isGroupLikeElem_of (g : G) : IsGroupLikeElem R (of A G g) where
  isUnit := .map _ <| Group.isUnit _
  comul_eq_tmul_self := by simp; rfl

@[simp]
lemma isGroupLikeElem_single (g : G) : IsGroupLikeElem R (single g 1 : MonoidAlgebra A G) :=
  isGroupLikeElem_of _

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

private noncomputable def hopfHomToMap (f : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) : G → H :=
  fun g ↦ (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose

@[simp]
private lemma single_hopfHomToMap_one (f : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) (g : G) :
    single (hopfHomToMap f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_of g).map f).choose_spec

open Coalgebra in
noncomputable
def hopfHomToMonoidHom (f : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) : G →* H where
  toFun := hopfHomToMap f
  map_one' := of_injective (k := K) <| by simp [← one_def]
  map_mul' g₁ g₂ := by
    refine of_injective (k := K) ?_
    simp only [of_apply, single_hopfHomToMap_one]
    rw [← mul_one (1 : K), ← single_mul_single, ← single_mul_single, map_mul]
    simp

@[simp]
protected lemma single_hopfHomToMonoidHom (f : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) (g : G)
    (k : K) : single (hopfHomToMap f g) k = f (single g k) := by
  rw [← mul_one k, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul]
  exact congr(k • $(single_hopfHomToMap_one f g))

@[simps] noncomputable
def monoidHomToHopfHom (f : G →* H) : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H where
  __ := MonoidAlgebra.mapDomainAlgHom K K f
  map_smul' m x := by simp
  counit_comp := by ext; simp
  map_comp_comul := by ext; simp

example {A : Type*} [Semiring A] [Algebra K A] (α β : MonoidAlgebra K G →ₐ[K] A)
    (hyp : ∀ g : G, α (single g 1) = β (single g 1)) : α = β := by exact algHom_ext hyp

private lemma aux1 {α : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H} {x : MonoidAlgebra K G} :
    α x = (α : _ →ₐ[K] _) x := rfl

private lemma aux2 {α β : MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H}
    (hyp : (α : _ →ₐ _) = (β : MonoidAlgebra K G →ₐ[K] MonoidAlgebra K H)) : α = β := by
  ext1 x
  rw [aux1, aux1]
  exact congr($(hyp) x)

noncomputable
def hopfHomEquivMonoidHom : (MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) ≃ (G →* H) where
  toFun f := hopfHomToMonoidHom f
  invFun f := monoidHomToHopfHom f
  left_inv f := by
    simp
    apply aux2
    apply algHom_ext
    intro x
    simp
    rw [← single_hopfHomToMap_one]
    rfl
  right_inv f := by
    ext g
    apply of_injective (k := K)
    simp
    show single (MonoidAlgebra.hopfHomToMap.{u_1, u_4, u_5} (K := K)
        (MonoidAlgebra.monoidHomToHopfHom f) g) 1 = _
    rw [MonoidAlgebra.single_hopfHomToMonoidHom]
    show (mapDomainRingHom K f) (single g 1) = single (f g) 1
    rw [MonoidAlgebra.mapDomainRingHom_apply]
    simp

end Group

section CommGroup

variable [CommGroup H]

--TODO: Yaël fix diamonds!!!!!!!!!!!!!!!!!!!!!!!!
noncomputable
instance : Group <| MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H := hopfHomEquivMonoidHom.group

end CommGroup

end Field

end MonoidAlgebra
