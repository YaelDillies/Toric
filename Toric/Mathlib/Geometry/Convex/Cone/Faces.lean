import Toric.Mathlib.Geometry.Convex.Cone.Polyhedral
import Toric.Mathlib.LinearAlgebra.PerfectPairing.Basic

lemma ex_imp_of_imp_ex {α : Type*} [hα : Nonempty α] {P : Prop} {Q : α → Prop} :
    (P → ∃ x, Q x) → ∃ x, P → Q x := by
  intro h
  by_cases hP : P
  · tauto
  · use Classical.choice hα
    tauto

theorem Finset.exists_le'
    {α β : Type*} [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)] [DecidableEq β]
    (s : Finset α) (f : α → β) : ∃ M, ∀ i ∈ s, f i ≤ M := by
  let ⟨M, hM⟩ := Finset.exists_le (image f s)
  use M
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hM
  assumption

theorem Finset.exists_lt'
    {α β : Type*} [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)] [NoMaxOrder β] [DecidableEq β]
    (s : Finset α) (f : α → β) : ∃ M, ∀ i ∈ s, f i < M := by
  obtain ⟨M, hM⟩ := Finset.exists_le' s f
  obtain ⟨N, hN⟩ := exists_gt M
  use N
  exact fun i hi => lt_of_le_of_lt (hM i hi) hN

theorem eq_zero_of_nonneg_add
    {α : Type*} [AddGroup α] [PartialOrder α] [AddLeftMono α] {a b : α} :
    0 ≤ a → 0 ≤ b → a + b = 0 → a = 0 ∧ b = 0 := fun ha hb hab => by
  constructor
  · apply eq_neg_of_add_eq_zero_right at hab
    rw [hab, Left.nonneg_neg_iff] at hb
    exact le_antisymm hb ha
  · apply eq_neg_of_add_eq_zero_left at hab
    rw [hab, Left.nonneg_neg_iff] at ha
    exact le_antisymm ha hb


open Submodule Pointwise LinearMap

namespace PointedCone

section Definitions

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
def perp (u : M) : PointedCone R N where
    carrier := {v | p u v = 0}
    add_mem' {v v'} hv hv' := by simp [Set.mem_setOf_eq ▸ hv, Set.mem_setOf_eq ▸ hv']
    zero_mem' := by simp
    smul_mem' c {v} hv := by simp [Set.mem_setOf_eq ▸ hv]

@[simp] lemma mem_perp {u : M} {v : N} : v ∈ perp p u ↔ p u v = 0 := by simp [perp, comm]
@[simp] lemma perp_zero : perp p 0 = ⊤ := by ext; simp

variable (p) in
def IsFace (c : PointedCone R N) (f : PointedCone R N) : Prop :=
  ∃ u ∈ dual' p.flip c, f = c ⊓ perp p u

lemma isFace_subset {c : PointedCone R N} {f : PointedCone R N} (h : IsFace p c f) : f ≤ c := by
  obtain ⟨h₁, ⟨h₂, h₃⟩⟩ := h
  simp [h₃]

theorem face_polyhedral
    {c : PointedCone R N} (hc : IsPolyhedral p c)
    {f : PointedCone R N} (hf : IsFace p c f) : IsPolyhedral p f := by
  obtain ⟨S, hS₁, hS₂⟩ := hc
  subst hS₂
  obtain ⟨u, hu₁, hu₂⟩ := hf
  subst hu₂
  use (insert (-u) S)
  apply And.intro (Set.Finite.insert _ hS₁)
  ext v
  rw [dual_insert, Submodule.mem_inf, Submodule.mem_inf]
  constructor
  · rintro ⟨hv₁, hv₂⟩
    apply And.intro hv₂ (le_antisymm _ _)
    · rwa [mem_dual'_singleton, map_neg, LinearMap.neg_apply, Left.nonneg_neg_iff] at hv₁
    · exact hu₁ hv₂
  · intro ⟨hv₁, hv₂⟩
    apply And.intro _ hv₁
    simp [mem_perp.mp hv₂]

theorem face_int
    {c : PointedCone R N}
    {f : PointedCone R N} (hf : IsFace p c f)
    {f' : PointedCone R N} (hf' : IsFace p c f') :
    IsFace p c (f ⊓ f') := by
  obtain ⟨u, hu₁, hu₂⟩ := hf
  subst hu₂
  obtain ⟨u', hu'₁, hu'₂⟩ := hf'
  subst hu'₂
  use u + u'
  apply And.intro (add_mem hu₁ hu'₁)
  ext v
  constructor
  · intro hv
    obtain ⟨⟨hv₁, hv₂⟩, ⟨-, hv₃⟩⟩ := hv
    apply And.intro hv₁
    rw [SetLike.mem_coe, mem_perp] at hv₂ hv₃
    simp [hv₂, hv₃]
  · intro ⟨hv₁, hv₂⟩
    rw [SetLike.mem_coe] at hv₁ hv₂
    specialize hu₁ hv₁
    specialize hu'₁ hv₁
    rw [LinearMap.flip_apply] at hu₁ hu'₁
    rw [mem_perp, map_add, LinearMap.add_apply] at hv₂
    obtain ⟨huv, hu'v⟩ := eq_zero_of_nonneg_add hu₁ hu'₁ hv₂
    trivial

theorem add_mem_face
    {c : PointedCone R N}
    {f : PointedCone R N} (hf : IsFace p c f)
    {v : N} {hv : v ∈ c} {w : N} {hw : w ∈ c} :
    v + w ∈ f → v ∈ f ∧ w ∈ f := fun h => by
  obtain ⟨u, hu₁, hu₂⟩ := hf
  subst hu₂
  obtain ⟨h₁, h₂⟩ := h
  rw [SetLike.mem_coe, mem_perp, map_add] at h₂
  have ⟨huv, huw⟩ := eq_zero_of_nonneg_add (hu₁ hv) (hu₁ hw) h₂
  trivial

end Definitions


section LinearOrder

variable {R M N : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

theorem face_face (hR : ∀ (x y : R), 0 < y → ∃ z, 0 < z * y + x)
    {c : PointedCone R N} (hc : c.FG)
    {f : PointedCone R N} (hf : IsFace p c f)
    {f' : PointedCone R N} (hf' : IsFace p f f') :
    IsFace p c f' := by
  obtain ⟨u, hu₁, hu₂⟩ := hf
  subst hu₂
  obtain ⟨u', hu'₁, hu'₂⟩ := hf'
  subst hu'₂
  obtain ⟨S, hS⟩ := hc
  have hSc : ∀ v ∈ S, v ∈ c := fun v hv => hS ▸ subset_span hv
  obtain h_for_ex : ∀ v ∈ S, 0 < p u v → ∃ r : R, 0 < p (r • u + u') v := by
    intro v hv huv
    obtain ⟨n, hn⟩ := hR (p u' v) (p u v) huv
    use n
    simpa
  obtain ⟨rf, hrf⟩ : ∃ (r : N → R), ∀ v ∈ S, 0 < p u v → 0 < p (r v • u + u') v := by
    apply Classical.axiomOfChoice (r := fun v r => _ → _ → 0 < p (r • u + u') v)
    exact fun _ => ex_imp_of_imp_ex (fun hv => ex_imp_of_imp_ex (h_for_ex _ hv))
  obtain ⟨r, hr⟩ := Finset.exists_le' S rf
  have HS : ∀ v ∈ S, 0 ≤ p (r • u + u') v ∧
      (p (r • u + u') v = 0 ↔ p u v = 0 ∧ p u' v = 0) := fun v hv => by
    have huv : 0 ≤ p u v := hu₁ (hSc _ hv)
    rcases lt_or_eq_of_le huv with huv₁ | huv₂
    · have H : 0 < (p (r • u + u')) v := by
        apply lt_of_lt_of_le (hrf _ hv huv₁)
        simp [huv₁, hv, hr]
      apply And.intro (le_of_lt H)
      constructor <;> aesop
    · have hu'v : 0 ≤ p u' v := by tauto
      simp [←huv₂, hu'v]
  have H : ∀ v ∈ c, 0 ≤ p (r • u + u') v ∧
      (p (r • u + u') v = 0 ↔ p u v = 0 ∧ p u' v = 0) := fun v hv => by
    rw [iff_def, ←and_assoc]
    apply And.intro _ (by rintro ⟨huv, hu'v⟩; simp [huv, hu'v])
    obtain ⟨l, hl, hlv⟩ := Submodule.mem_span_finset.mp (hS ▸ hv)
    simp_rw [←Nonneg.coe_smul] at hlv
    subst hlv
    simp_rw [map_sum, map_smul_of_tower]
    have hnn := fun w hw => smul_nonneg (l w).2 (HS w hw).1
    apply And.intro (Finset.sum_nonneg hnn)
    intro H
    have h_ruu'_zero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp H
    simp_rw [smul_eq_zero] at h_ruu'_zero
    have h_or_zero := fun i hi => Or.imp_right (HS i hi).2.mp (h_ruu'_zero i hi)
    simp_rw [or_and_left] at h_or_zero
    have hu_zero := fun i hi => smul_eq_zero.mpr (h_or_zero i hi).1
    have hu'_zero := fun i hi => smul_eq_zero.mpr (h_or_zero i hi).2
    constructor <;> apply Finset.sum_eq_zero <;> assumption
  use r • u + u'
  constructor
  · apply fun v hv => (H v hv).1
  · ext v
    simp_rw [mem_inf, mem_perp]
    have := fun hv => (H v hv).2
    tauto

end LinearOrder

end PointedCone


open PointedCone


section Definition

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
structure PolyhedralCone extends PointedCone R N where
  isPolyhedral : IsPolyhedral p toSubmodule

namespace PolyhedralCone

attribute [coe] toSubmodule

instance : CoeOut (PolyhedralCone p) (PointedCone R N) := ⟨toSubmodule⟩

@[ext]
theorem ext {c c' : PolyhedralCone p} (h : (c : PointedCone R N) = c') : c = c' :=
  by cases c; cases c'; congr

instance : SetLike (PolyhedralCone p) N where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

end PolyhedralCone

end Definition


namespace PolyhedralCone

variable {𝕜 M N : Type*}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup M] [AddCommGroup N]
  [Module 𝕜 M] [Module.Finite 𝕜 M]
  [Module 𝕜 N] [Module.Finite 𝕜 N]
  (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) {hp : IsPerfPair p}

instance : LE (PolyhedralCone p) := {le := fun f f' => IsFace p f f'}

instance : PartialOrder (PolyhedralCone p) := {
  le_refl := by {intro a; use 0; constructor <;> simp}
  lt := fun a b => a ≤ b ∧ ¬ b ≤ a
  le_trans := fun a b c ha hb => by {
    have hafg := fg_of_isPolyhedral hp.bijective_left.injective
      hp.bijective_right.injective a.isPolyhedral
    have hR : ∀ (x y : 𝕜), 0 < y → ∃ z, 0 < z * y + x := fun x y hy => by
      use - (x - 1) / y
      field_simp
    exact face_face hR hafg ha hb
  }
  le_antisymm := fun a b hab hba => ext (antisymm (isFace_subset hba) (isFace_subset hab))
}

abbrev IsFacet (a b : PolyhedralCone p) := a ⋖ b

end PolyhedralCone
