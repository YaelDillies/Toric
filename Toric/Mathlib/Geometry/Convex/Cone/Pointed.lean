import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.FiniteDimensional.Defs


namespace PointedCone

section Semiring

variable {R E : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E]
  [Module R E] (s : Set E)

variable (R) in
abbrev span : PointedCone R E := Submodule.span {c : R // 0 ≤ c} s

lemma subset_span : s ⊆ span R s := Submodule.subset_span

lemma span_union (s t : Set E) : span R (s ∪ t) = span R s ⊔ span R t :=
  Submodule.span_union s t

def of_Submodule (c : Submodule R E) : PointedCone R E where
  carrier := c.carrier
  add_mem' := c.add_mem'
  zero_mem' := c.zero_mem'
  smul_mem' t x hx := by
    rw [Nonneg.mk_smul]
    exact c.smul_mem _ hx

lemma coe_of_Submodule (c : Submodule R E) : (of_Submodule c : Set E) = c :=
  rfl

@[simp]
lemma mem_of_Submodule (c : Submodule R E) (x : E) : x ∈ of_Submodule c ↔ x ∈ c := Iff.rfl

lemma span_le_of_Submodule : span R s ≤ of_Submodule (Submodule.span R s) :=
  Submodule.span_le.mpr (fun _x hx => Submodule.subset_span hx)

end Semiring 


section Ring

variable {R E : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E]
  [Module R E] (s : Set E)

lemma span_neg_le_of_Submodule : span R (-s) ≤ of_Submodule (Submodule.span R s) := by
  rw [Submodule.span_le]
  intro x hx
  convert Submodule.smul_mem (Submodule.span R s) (-1) (Submodule.subset_span hx)
  simp only [smul_neg, neg_smul, one_smul, neg_neg]

theorem of_Submodule_eq_span : of_Submodule (Submodule.span R s) = span R (s ∪ -s) := by
  apply le_antisymm
  · intro x hx
    rw [mem_of_Submodule] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Set.mem_union_left _ hx)
    | zero => exact Submodule.zero_mem _
    | add x y _hx _hy hx hy => exact Submodule.add_mem _ hx hy
    | smul t x hx1 hx2 => sorry
  · rw [span_union]
    exact sup_le (span_le_of_Submodule s) (span_neg_le_of_Submodule s)

section LinearOrderedField

variable {𝕜 E : Type*} [Field 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

theorem PointedCone.fg [hE : FiniteDimensional 𝕜 E] (c : PointedCone 𝕜 E) : c.FG := by
  classical
  obtain ⟨S,hS⟩ := Module.finite_def.mp hE
  rw [Submodule.fg_def]
  use S ∪ -S
  split_ands
  · simp only [Set.involutiveNeg, Set.finite_union, Finset.finite_toSet, Set.finite_neg, and_self]
  · sorry

end LinearOrderedField
