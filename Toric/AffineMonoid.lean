import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.FreeModule.PID
import Toric.Mathlib.GroupTheory.MonoidLocalization.Basic

-- TODO: wrong torsion-free definition? move?
@[to_additive IsAddFree]
def IsMultFree (M) [Monoid M] := ∀ (n : ℕ), Function.Injective (fun (x : M) ↦ x^n)

/-- The product of finitely generated monoids is finitely generated. -/
@[to_additive "The product of finitely generated monoids is finitely generated."]
instance FG_prod_FG {M N} [Monoid M] [Monoid N] [hM : Monoid.FG M] [hN : Monoid.FG N] :
    Monoid.FG (M × N) := by
  obtain ⟨bM, hbM⟩ := hM
  obtain ⟨bN, hbN⟩ := hN
  classical
  refine ⟨(bM ×ˢ singleton 1) ∪ (singleton 1 ×ˢ bN), ?_⟩
  ext ⟨x, y⟩; simp
  rintro _ ⟨S, rfl⟩ _ ⟨hS, rfl⟩
  simp at hS ⊢
  obtain ⟨hS1, hS2⟩ := hS
  suffices parts : (x, 1) ∈ S ∧ (1, y) ∈ S by simpa using Submonoid.mul_mem S parts.1 parts.2

  refine ⟨?_, ?_⟩
  · let fst : Submonoid M := {
      carrier : Set M := (fun i ↦ (i, (1 : N))) ⁻¹' S
      mul_mem' ha hb := by simpa [Prod.mk_mul_mk, mul_one] using Submonoid.mul_mem S ha hb
      one_mem' := by simp [Submonoid.one_mem S]
    }
    have fst_eq_top : fst = ⊤ := by
      have : bM.toSet ⊆ fst := hS1
      rwa [← Submonoid.closure_le, hbM, top_le_iff] at this
    have xfst : x ∈ fst := by rw [fst_eq_top]; trivial
    exact xfst
  · let snd : Submonoid N := {
      carrier : Set N := (fun i ↦ ((1 : M), i)) ⁻¹' S
      mul_mem' ha hb := by simpa [Prod.mk_mul_mk, mul_one] using Submonoid.mul_mem S ha hb
      one_mem' := by simp [Submonoid.one_mem S]
    }
    have snd_eq_top : snd = ⊤ := by
      have : bN.toSet ⊆ snd := hS2
      rwa [← Submonoid.closure_le, hbN, top_le_iff] at this
    have ysnd : y ∈ snd := by rw [snd_eq_top]; trivial
    exact ysnd

namespace Localization

/-- The localization of a finitely generated monoid at a finitely generated submonoid
is finitely generated. -/
@[to_additive "The localization of a finitely generated monoid at a finitely generated submonoid is finitely generated."]
instance FG_loc_of_FG {M} [CommMonoid M] [hM : Monoid.FG M] {N : Submonoid M} (hN : N.FG) :
    Monoid.FG <| Localization N := by
  let antidiagonal : (M × N) →* Localization N := {
    toFun x := Localization.mk x.1 ⟨x.2, by simp only [SetLike.coe_mem]⟩
    map_one' := Localization.mk_one
    map_mul' x y := by rw [Localization.mk_mul x.1 y.1 ⟨x.2, _⟩ ⟨y.2, _⟩]; rfl
  }
  have hNFG : Monoid.FG N := (Monoid.fg_iff_submonoid_fg _).mpr hN
  refine Monoid.fg_of_surjective antidiagonal ?_
  rintro ⟨x, y⟩; exact ⟨⟨x, y⟩, rfl⟩

/-- All elements of the localization come from `mk`. -/
@[to_additive "All elements of the localization come from `mk`."]
lemma mk_of {M} [CommMonoid M] {N : Submonoid M} (g : Localization N) : ∃ x y, mk x y = g := by
  obtain ⟨x, y⟩ := g
  refine ⟨x, y, rfl⟩

/-- The localization of a torsion-free monoid is torsion-free. -/
@[to_additive "The localization of a torsion-free monoid is torsion-free."]
instance torsionFree_of_torsionFree {M} [CommMonoid M] {hM : IsMultFree M} {N : Submonoid M} :
    Monoid.IsTorsionFree <| Localization N := by
  rintro g hg
  rw [isOfFinOrder_iff_pow_eq_one]
  simp only [not_exists, not_and]
  intros n hn hgn
  obtain ⟨x, y, rfl⟩ := mk_of g
  rw [mk_pow, ← mk_one, mk_eq_mk_iff, r_iff_exists] at hgn
  obtain ⟨c, hc⟩ := hgn
  simp at hc
  refine Function.not_injective_iff.mpr ⟨c * x, c * y, ?_, fun hxy ↦ hg ?_⟩ <| hM n
  cases n
  . simp
  . rw [mul_pow, mul_pow, pow_add, pow_one, mul_assoc, hc, ← mul_assoc]
  rw [← mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨c, by simpa⟩

/-- The natural map from a cancellative monoid into its localization is injective.-/
@[to_additive mk_inj_of_cancelAdd "The natural map from a cancellative monoid into its localization is injective."]
lemma mk_inj_of_cancelMul {M} [CommMonoid M] [hM : IsCancelMul M] {N : Submonoid M} :
    Function.Injective <| (monoidOf N).toFun := fun x y hxy ↦ by
  obtain ⟨_, hc⟩ := r_iff_exists.mp <| mk_eq_mk_iff.mp hxy
  simpa using mul_left_cancel hc

end Localization

--

variable {S : Type*} [AddCommMonoid S] [hFG : AddMonoid.FG S] [IsCancelAdd S]

instance affine_monoid_imp_lattice_embedding {hS : IsAddFree S} :
    Module.Free ℤ <| AddLocalization (⊤ : AddSubmonoid S) := by
  have : AddMonoid.FG <| AddLocalization (⊤ : AddSubmonoid S) :=
    AddLocalization.FG_loc_of_FG <| AddMonoid.fg_def.mp hFG
  have _ := Module.Finite.iff_addGroup_fg.mpr <| AddGroup.fg_iff_addMonoid_fg.mpr this
  refine Module.free_iff_noZeroSMulDivisors.mpr <| (noZeroSMulDivisors_iff _ _).mpr ?_
  intro n g hng
  by_contra h
  obtain ⟨hn, hg⟩ := not_or.mp h
  exact AddLocalization.torsionFree_of_torsionFree (hM := hS) g hg <| isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨n, hn, hng⟩
-- lemma affine_monoid_imp_lattice_embedding {hS : IsAddFree S} :
--     ∃ (n : ℕ) (f : S →+ FreeAbelianGroup (Fin n)), Function.Injective f := by
--   let G := AddLocalization (⊤ : AddSubmonoid S)
--   set locmap : S →+ G := {
--     toFun x := AddLocalization.mk x 0
--     map_zero' := AddLocalization.mk_zero
--     map_add' x y := by rw [AddLocalization.mk_add x y 0 0, add_zero]
--   }

--   have hGemb : Function.Injective locmap.toFun := by
--     intros m m' hm
--     rw [AddLocalization.mk_eq_mk_iff, AddLocalization.r_iff_exists] at hm
--     obtain ⟨c, hc⟩ := hm
--     simpa only [ZeroMemClass.coe_zero, zero_add, add_right_inj] using hc

--   have hGfg : AddGroup.FG G := AddGroup.fg_iff_addMonoid_fg.mpr <| by
--     let antidiagonal : (S × S) →+ G := {
--       toFun x := AddLocalization.mk x.1 ⟨x.2, trivial⟩
--       map_zero' := AddLocalization.mk_zero
--       map_add' x y := by rw [AddLocalization.mk_add x.1 y.1 ⟨x.2, _⟩ ⟨y.2, _⟩]; rfl
--     }
--     refine AddMonoid.fg_of_surjective antidiagonal ?_
--     rintro ⟨x, y⟩; exact ⟨⟨x, y⟩, rfl⟩

--   have hGtf : AddMonoid.IsTorsionFree G := by
--     rintro ⟨x, y⟩ hg ⟨n, hnpos, hn⟩
--     refine hg ?_
--     sorry

--   have hGfree : Module.Free ℤ G := by -- structure theorem + torsion free
--     have _ := Module.Finite.iff_addGroup_fg.mpr hGfg
--     refine Module.free_iff_noZeroSMulDivisors.mpr <| (noZeroSMulDivisors_iff _ _).mpr ?_
--     intro n g hg
--     by_contra h
--     obtain ⟨hn, hg₂⟩ := not_or.mp h
--     exact hGtf g hg₂ <| isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨n, hn, hg⟩
--   sorry
