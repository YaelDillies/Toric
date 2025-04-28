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

lemma coe_of_Submodule (c : Submodule R E) : (of_Submodule c : Set E) = c := rfl

@[simp]
lemma mem_of_Submodule (c : Submodule R E) (x : E) : x ∈ of_Submodule c ↔ x ∈ c := Iff.rfl

@[simp]
lemma of_Submodule_top : of_Submodule (⊤ : Submodule R E) = ⊤ := rfl

@[simp]
lemma of_Submodule_bot : of_Submodule (⊥ : Submodule R E) = ⊥ := rfl

lemma span_le_of_Submodule : span R s ≤ of_Submodule (Submodule.span R s) :=
  Submodule.span_le.mpr (fun _x hx => Submodule.subset_span hx)

end Semiring 


section Ring

variable {R E : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup E]
  [Module R E] (s : Set E)

lemma span_neg_le_of_Submodule : span R (-s) ≤ of_Submodule (Submodule.span R s) := by
  rw [Submodule.span_le]
  intro x hx
  convert Submodule.smul_mem (Submodule.span R s) (-1) (Submodule.subset_span hx)
  simp only [smul_neg, neg_smul, one_smul, neg_neg]

lemma of_Submodule_eq_span.aux {x : E} (hx : x ∈ span R (s ∪ -s)) : -x ∈ span R (s ∪ -s) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    cases hx
    · apply Or.inr
      rw [Set.mem_neg, neg_neg]
      assumption
    · apply Or.inl
      assumption
  | zero => simp
  | add x y _hx bhy hx hy =>
    rw [neg_add_rev]
    exact Submodule.add_mem _ hy hx
  | smul t x hx1 hx2 =>
    rw [←smul_neg]
    exact Submodule.smul_mem (span R (s ∪ -s)) t hx2

lemma of_Submodule_eq_span : of_Submodule (Submodule.span R s) = span R (s ∪ -s) := by
  apply le_antisymm
  · intro x hx
    rw [mem_of_Submodule] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Set.mem_union_left _ hx)
    | zero => exact Submodule.zero_mem _
    | add x y _hx _hy hx hy => exact Submodule.add_mem _ hx hy
    | smul t x hx1 hx2 =>
      by_cases ht : 0 ≤ t
      · exact Submodule.smul_mem (span R (s ∪ -s)) ⟨t,ht⟩ hx2
      · replace hx2 := of_Submodule_eq_span.aux s hx2
        convert Submodule.smul_mem _ ⟨-t, neg_nonneg.mpr (not_le.mp ht).le⟩ hx2 using 1
        rw [Nonneg.mk_smul, smul_neg, neg_smul, neg_neg]
  · rw [span_union]
    exact sup_le (span_le_of_Submodule s) (span_neg_le_of_Submodule s)


section Field

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem top_fg [hE : FiniteDimensional 𝕜 E] : (⊤ : PointedCone 𝕜 E).FG := by
  obtain ⟨S,hS⟩ := Module.finite_def.mp hE
  rw [Submodule.fg_def]
  use S ∪ -S
  split_ands
  · simp only [Set.finite_union, Finset.finite_toSet, Set.finite_neg, and_self]
  · rw [←of_Submodule_top, ←hS, of_Submodule_eq_span]

end Field
