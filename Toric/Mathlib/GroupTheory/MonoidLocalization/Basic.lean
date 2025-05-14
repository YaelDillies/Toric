import Mathlib.Algebra.Group.Torsion
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.MonoidLocalization.Basic

open Function

namespace Localization
variable {M : Type*} [CommMonoid M] {N : Submonoid M}

/-- The localization of a finitely generated monoid at a finitely generated submonoid is
finitely generated. -/
@[to_additive "The localization of a finitely generated monoid at a finitely generated submonoid is
finitely generated."]
lemma fg [Monoid.FG M] (hN : N.FG) : Monoid.FG <| Localization N := by
  let antidiagonal : M × N →* Localization N := {
    toFun x := mk x.1 ⟨x.2, by simp only [SetLike.coe_mem]⟩
    map_one' := mk_one
    map_mul' x y := by rw [mk_mul x.1 y.1 ⟨x.2, _⟩ ⟨y.2, _⟩]; rfl
  }
  have hNFG : Monoid.FG N := (Monoid.fg_iff_submonoid_fg _).mpr hN
  refine Monoid.fg_of_surjective antidiagonal ?_
  rintro ⟨x, y⟩
  exact ⟨⟨x, y⟩, rfl⟩

/-- The Grothendieck group of a finitely generated monoid is finitely generated. -/
@[to_additive "The Grothendieck group of a finitely generated monoid is finitely generated."]
instance instFG [Monoid.FG M] : Monoid.FG <| Localization (⊤ : Submonoid M) := fg Monoid.FG.fg_top

/-- The localization of a torsion-free monoid is torsion-free. -/
@[to_additive "The localization of a torsion-free monoid is torsion-free."]
instance instIsMulTorsionFree [IsMulTorsionFree M] : IsMulTorsionFree <| Localization N where
  pow_left_injective n hn a b hab := by
    dsimp at hab
    induction' a using Localization.induction_on with a
    induction' b using Localization.induction_on with b
    simp only [mk_pow, mk_eq_mk_iff, r_iff_exists, SubmonoidClass.coe_pow, Subtype.exists,
      exists_prop] at hab ⊢
    obtain ⟨c, hc, hab⟩ := hab
    refine ⟨c, hc, pow_left_injective hn ?_⟩
    obtain _ | n := n
    · simp
    · simp [mul_pow, pow_succ c, mul_assoc, hab]

end Localization
