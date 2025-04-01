
/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
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
variable [Field K] [Group G] [Group H] {x : MonoidAlgebra K G}

open Submodule in
@[simp]
lemma isGroupLikeElem_iff_mem_range_of : IsGroupLikeElem K x ↔ x ∈ Set.range (of K G) where
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

noncomputable
def hopfHomEquivMonoidHom : (MonoidAlgebra K G →ₐc[K] MonoidAlgebra K H) ≃ (G →* H) where
  toFun f := hopfHomToMonoidHom f
  invFun f := sorry
  left_inv := sorry
  right_inv := sorry

end Field
end MonoidAlgebra
