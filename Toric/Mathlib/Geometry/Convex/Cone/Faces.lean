import Toric.Mathlib.Geometry.Convex.Cone.Polyhedral
import Mathlib.LinearAlgebra.PerfectPairing.Basic

section

variable {α β : Type*}

theorem Finset.exists_image_le [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)] [DecidableEq β]
    (s : Finset α) (f : α → β) : ∃ M, ∀ i ∈ s, f i ≤ M := by
  let ⟨M, hM⟩ := Finset.exists_le (image f s)
  use M
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hM
  assumption

theorem Finset.exists_image_lt
    [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)] [NoMaxOrder β] [DecidableEq β]
    (s : Finset α) (f : α → β) : ∃ M, ∀ i ∈ s, f i < M := by
  let ⟨M, hM⟩ := Finset.exists_image_le s f
  let ⟨N, hN⟩ := exists_gt M
  use N
  intro i hi
  exact lt_of_le_of_lt (hM i hi) hN

end


-- namespace Finset

-- universe u
-- variable {α : Type*} {β : Type*} {γ : Type*}

-- section Filter
-- variable (p : α → Prop) [DecidablePred p] (s : Finset α)

-- theorem filter_disj_union_filter :
--     disjUnion _ _ (Finset.disjoint_filter_filter_neg s s p) = s := by
--   ext x
--   rw [mem_disjUnion, mem_filter, mem_filter]
--   tauto

-- end Filter
-- end Finset


namespace PointedCone

open Pointwise

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M} {y : N}

variable (p) in
def perp (s : Set M) : PointedCone R N where
    carrier := {y | ∀ ⦃x⦄, x ∈ s → 0 = p x y}
    zero_mem' := by simp
    add_mem' {u v} hu hv x hx := by rw [map_add, ←hu hx, ←hv hx, add_zero]
    smul_mem' c y hy x hx := by rw [← Nonneg.coe_smul, map_smul, ←hy hx, smul_eq_mul, mul_zero]

@[simp] lemma mem_perp {s : Set M} {y : N} : y ∈ perp p s ↔ ∀ ⦃x⦄, x ∈ s → 0 = p x y := .rfl
@[simp] lemma mem_perp_singleton {x : M} {y : N} : y ∈ perp p {x} ↔ 0 = p x y := by simp

@[simp] lemma perp_empty : perp p ∅ = ⊤ := by ext; simp
@[simp] lemma perp_zero : perp p 0 = ⊤ := by ext; simp
@[simp] lemma perp_zero_singleton : perp p {0} = ⊤ := by ext; simp

variable (p) in
def IsFace (c : PointedCone R N) (f : PointedCone R N) : Prop :=
  ∃ x ∈ dual' p.flip c, f = perp p {x} ⊓ c

lemma isFace_subset {c : PointedCone R N} {f : PointedCone R N} (h : IsFace p c f) : f ≤ c := by
  let ⟨h₁, ⟨h₂, h₃⟩⟩ := h
  simp [h₃]

end PointedCone


namespace PointedCone

variable {R M N : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

theorem star [Module.Finite R N] [Module.Finite R M] {c : PointedCone R N}
    (hc : IsPolyhedral p c) : ∀ ⦃v₀⦄, v₀ ∉ c → ∃ u₀, u₀ ∈ (dual' p.flip c) ∧ p u₀ v₀ < 0 := by
  intro v₀ hv₀
  contrapose hv₀
  simp only [not_exists, not_and, not_lt] at hv₀
  simp only [not_not]
  rw [←IsPolyhedral.dual_dual_flip hc]
  assumption

theorem prop2 [Module.Finite R N] [Module.Finite R M]
    {c : PointedCone R N} (hc : IsPolyhedral p c)
    {f : PointedCone R N} (hf : IsFace p c f) : IsPolyhedral p f := by
  rcases hc with ⟨t, ht⟩
  rcases hf with ⟨x, hx1, hx2⟩
  classical
  use (insert (-x) t)
  ext y
  rw [Finset.coe_insert, dual_insert, Submodule.mem_inf, hx2, Submodule.mem_inf]
  constructor
  · intro hy
    rcases hy with ⟨hy1, hy2⟩
    constructor
    · rw [mem_perp] at hy1
      simp only [mem_dual', Set.mem_singleton_iff, forall_eq, map_neg, LinearMap.neg_apply,
        le_neg_self_iff, le_refl, ht, hy1]
    · rw [←ht]
      assumption
  · intro hy
    rcases hy with ⟨hy1, hy2⟩
    rw [←ht] at hy2
    constructor
    · simp only [mem_perp, Set.mem_singleton_iff, forall_eq]
      rw [le_antisymm_iff]
      constructor
      · apply hx1 hy2
      · simp only [mem_dual', Set.mem_singleton_iff, forall_eq, map_neg, LinearMap.neg_apply,
          Left.nonneg_neg_iff] at hy1
        assumption
    · assumption

theorem prop3 [Module.Finite R N] [Module.Finite R M]
    {c : PointedCone R N}
    {f : PointedCone R N} (hf : IsFace p c f)
    {f' : PointedCone R N} (hf' : IsFace p c f') :
    IsFace p c (f ⊓ f') := by
  rcases hf with ⟨x, hx1, hx2⟩
  rcases hf' with ⟨x', hx'1, hx'2⟩
  use x + x'
  constructor
  · exact add_mem hx1 hx'1
  · ext y
    constructor
    · intro hy
      rw [hx2, hx'2] at hy
      simp only [Submodule.mem_inf, mem_perp, Set.mem_singleton_iff, forall_eq] at hy
      rcases hy with ⟨⟨hy1, hy2⟩, hy3, -⟩
      simp only [Submodule.mem_inf, mem_perp, Set.mem_singleton_iff, forall_eq, map_add,
        LinearMap.add_apply]
      constructor
      · rw [←hy1, ←hy3, add_zero]
      · assumption
    · intro hy
      rcases hy with ⟨hy1, hy2⟩
      simp only [SetLike.mem_coe, mem_perp, Set.mem_singleton_iff, forall_eq, map_add,
        LinearMap.add_apply] at hy1
      have hxy := hx1 hy2
      have hx'y := hx'1 hy2
      rw [LinearMap.flip_apply] at hxy
      rw [LinearMap.flip_apply] at hx'y
      rw [hx2, hx'2]
      constructor <;> simp only [Submodule.inf_coe, Set.mem_inter_iff, SetLike.mem_coe, mem_perp,
        Set.mem_singleton_iff, forall_eq] <;> constructor
      · linarith
      · assumption
      · linarith
      · assumption

open LinearMap

theorem prop4 (hR : ∀ (x y : R), 0 < y → ∃ z, x < z * y)
    {c : PointedCone R N} (hc : c.FG)
    {f : PointedCone R N} (hf : IsFace p c f)
    {f' : PointedCone R N} (hf' : IsFace p f f') :
    IsFace p c f' := by
  let ⟨u, hu, hfu⟩ := hf
  let ⟨u', hu', hf'u'⟩ := hf'
  let ⟨n, H⟩ : ∃ n : R, ∀ v ∈ c, 0 < p u v → 0 < p (n • u + u') v := by
    let ⟨S, hS⟩ := hc
    let ⟨n, hn⟩ : ∃ (n : R), ∀ v ∈ S, 0 < p u v → 0 < p (n • u + u') v := by
      have hfe : ∀ v ∈ S, 0 < p u v → ∃ n : R, 0 < p (n • u + u') v := by
        intro v hv huv
        let ⟨n, hn⟩ := hR (- p u' v) (p u v) huv
        use n
        simp only [map_add, map_smul, add_apply, smul_apply]
        simp only [smul_eq_mul]
        linarith
      let ⟨n, hn⟩ : ∃ (n : N → R), ∀ v : N, v ∈ {v ∈ S | 0 < p u v} → 0 < p (n v • u + u') v := by
        apply @Classical.axiomOfChoice _ _ (fun v n => _ → 0 < p (n • u + u') v)
        intro v
        by_cases h : v ∈ {v ∈ S | 0 < (p u) v}
        · let ⟨n, hn⟩ := And.elim (hfe v) (Finset.mem_filter.mp h)
          use n
          intro h2
          assumption
        · use 0
          intro h2
          contradiction
      let ⟨M, hM⟩ := Finset.exists_image_lt {v ∈ S | 0 < p u v} n
      use M
      intro v hv huv
      have hMv := hM v (Finset.mem_filter.mpr ⟨hv, huv⟩)
      have hnv := hn v (Finset.mem_filter.mpr ⟨hv, huv⟩)
      simp only [map_add, map_smul_of_tower, add_apply, smul_apply, gt_iff_lt]
      rw [←sub_lt_iff_lt_add]
      simp only [map_add, map_smul_of_tower, add_apply, smul_apply, smul_eq_mul] at hnv
      rw [smul_eq_mul]
      apply lt_trans' ((mul_lt_mul_right huv).mpr hMv)
      rw [sub_lt_iff_lt_add]
      assumption
    use n
    intro v hv huv
    rw [←hS] at hv
    let ⟨h, hh, hvc⟩ := Submodule.mem_span_finset.mp hv
    let ⟨s, hs, hus, hhs⟩ : ∃ s ∈ S, 0 < p u s ∧ 0 < h s := by
      contrapose huv
      rw [not_lt]
      simp_rw [not_exists, not_and, not_lt] at huv
      simp_rw [←hvc, map_sum, map_smul_of_tower]
      apply Finset.sum_nonpos
      intro i hi
      have hui : 0 ≤ (p u) i := by
        apply hu
        rw [SetLike.mem_coe, ←hS]
        apply Set.mem_of_mem_of_subset hi
        apply Submodule.subset_span
      rcases lt_or_eq_of_le hui with hui | hui
      · have hhi : h i = 0 := by
          apply ge_antisymm
          · simp
          · exact huv i hi hui
        rw [hhi, zero_smul]
      · rw [←hui, smul_zero]
    rw [←hvc]
    simp only [map_sum, map_smul_of_tower]
    apply Finset.sum_pos'
    · intro i hi
      apply smul_nonneg
      · simp
      · have hui : 0 ≤ (p u) i := by
          apply hu
          rw [SetLike.mem_coe, ←hS]
          apply Set.mem_of_mem_of_subset hi
          apply Submodule.subset_span
        rcases lt_or_eq_of_le hui with hui | hui
        · apply le_of_lt
          apply hn i hi hui
        · have hu'i : 0 ≤ p u' i := by
            apply hu'
            rw [hfu]
            simp only [Submodule.inf_coe, Set.mem_inter_iff, SetLike.mem_coe,
              mem_perp_singleton, forall_eq]
            constructor
            · assumption
            · rw [←hS]
              apply Set.mem_of_mem_of_subset hi
              apply Submodule.subset_span
          simp [←hui, hu'i]
    · use s
      constructor
      · assumption
      · apply smul_pos
        · assumption
        · exact hn s hs hus
  use n • u + u'
  constructor
  · intro v hv
    have huv := hu hv
    rw [LinearMap.flip_apply, le_iff_lt_or_eq] at huv
    rw [LinearMap.flip_apply]
    rcases huv with huv | huv
    · exact le_of_lt (H _ hv huv)
    · have hu'v : 0 ≤ (p u') v := by
        simp only [mem_dual', SetLike.mem_coe, LinearMap.flip_apply] at hu'
        apply hu'
        rw [hfu, Submodule.mem_inf, mem_perp_singleton, ←huv]
        tauto
      rw [map_add, map_smul_of_tower, add_apply, smul_apply]
      rw [←huv, smul_zero, zero_add]
      assumption
  · ext v
    constructor
    · intro hv
      obtain ⟨hv₁, hv₂⟩ := hf'u' ▸ hv
      obtain ⟨hv₃, hv₄⟩ := hfu ▸ hv₂
      constructor
      · rw [SetLike.mem_coe, mem_perp_singleton] at *
        rw [map_add, map_smul_of_tower, add_apply, smul_apply]
        rw [←hv₁, ←hv₃, smul_zero, zero_add]
      · assumption
    · intro hv
      obtain ⟨hv₁, hv₂⟩ := hv
      have huv := hu hv₂
      rw [LinearMap.flip_apply, le_iff_lt_or_eq] at huv
      rw [SetLike.mem_coe, mem_perp_singleton] at hv₁
      rw [map_add, map_smul_of_tower, add_apply, smul_apply] at hv₁
      rcases huv with huv | huv
      · have := H v hv₂ huv
        rw [map_add, map_smul_of_tower, add_apply, smul_apply] at this
        exact False.elim (ne_of_lt this hv₁)
      · rw [hf'u', hfu]
        rw [←huv, smul_zero, zero_add] at hv₁
        rw [Submodule.mem_inf, mem_perp_singleton, Submodule.mem_inf, mem_perp_singleton]
        tauto

end PointedCone


namespace PointedCone

universe u v w u'

structure PolyhedralCone (R : Type u) [CommRing R] [PartialOrder R] [IsOrderedRing R]
  (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]
  (p : M →ₗ[R] N →ₗ[R] R) extends PointedCone R N where
  isPolyhedral : IsPolyhedral p toSubmodule

-- structure PolyhedralCone {R : Type u} [CommRing R] [PartialOrder R] [IsOrderedRing R]
--   {M : Type v} [AddCommGroup M] [Module R M]
--   {N : Type w} [AddCommGroup N] [Module R N]
--   (p : M → R M N) extends PointedCone R N where
--   isPolyhedral : IsPolyhedral p.toLinearMap toSubmodule

end PointedCone

namespace PointedCone

universe u v w u'

variable {𝕜 : Type u} {M : Type v} {N : Type w}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup M] [AddCommGroup N]
  [Module 𝕜 M] [Module.Finite 𝕜 M]
  [Module 𝕜 N] [Module.Finite 𝕜 N]
  (p : PerfectPairing 𝕜 M N)

@[coe]
def toPointedCone (c : PolyhedralCone 𝕜 M N p) : PointedCone 𝕜 N := c.toSubmodule


-- initialize_simps_projections PolyhedralCone (carrier → coe, as_prefix coe)

instance setLike : SetLike (PolyhedralCone p) N where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h

-- @[simp] lemma carrier_eq_coe (c : PolyhedralCone p.toLinearMap) : c.carrier = c := rfl

@[simp] theorem toModule_inj {c c' : PolyhedralCone p} :
    c.toSubmodule = c'.toSubmodule ↔ c = c' := by sorry

instance partialOrder' : PartialOrder (PolyhedralCone p) := sorry

instance partialOrder : PartialOrder (PolyhedralCone 𝕜 M N p) := {
  le := fun f f' => IsFace p.toLinearMap f.toSubmodule f'.toSubmodule
  lt := fun f f' => IsFace p.toLinearMap f.toSubmodule f'.toSubmodule ∧
    ¬ IsFace p.toLinearMap f'.toSubmodule f.toSubmodule
  le_refl := by {intro a; use 0; constructor <;> simp}
  le_trans := by {
    intro a b c ha hb
    have hafg := fg_of_isPolyhedral p.bijective_left.injective
      p.bijective_right.injective a.isPolyhedral
    have hR : ∀ (x y : 𝕜), 0 < y → ∃ z, x < z * y := by
      intro x y hy
      use (x + 1) / y
      rw [IsUnit.div_mul_cancel]
      · rw [lt_add_iff_pos_right]
        exact zero_lt_one
      · rw [isUnit_iff_ne_zero]
        exact ne_of_gt hy
    exact prop4 hR hafg ha hb
  }
  le_antisymm := by {
    intro a b hab hba
    apply isFace_subset at hab
    apply isFace_subset at hba
    apply (toModule_inj p).mp
    apply le_antisymm hba hab
  }
}

def top_to_pointedCone : PointedCone 𝕜 (⊤ : Submodule 𝕜 N) := by
  unfold PointedCone
  have : Submodule 𝕜 ⊤ := by sorry

lemma bot_polyhedral : IsPolyhedral p.toLinearMap ⊥ := by
  let ⟨S, hS⟩ := (@Module.finite_def 𝕜 M _ _ _).mp (by assumption)
  use S
  rw [←dual_span, ←Submodule.zero_eq_bot]
  symm
  unfold span
  have := Set.univ = ↑(span 𝕜 ↑S) := by

  apply dual_univ p.bijective_right.injective


instance orderBot : OrderBot (PolyhedralCone p.toLinearMap) := {
  bot := ⟨⊥, bot_polyhedral p⟩
  bot_le := by {
    intro a
    sorry
  }
}

def IsFacet (a b : PolyhedralCone p) := @IsCoatom (Set.Iic a) _ _ b
def IsEdge (a b : PolyhedralCone p) := @IsAtom (Set.Iic a) _ _ b

end PointedCone
