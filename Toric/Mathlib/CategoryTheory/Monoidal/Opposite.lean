import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite

namespace CategoryTheory

open MonoidalCategory Functor LaxMonoidal OplaxMonoidal

universe u₁ v₁ u₂ v₂
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

instance monoidalOpOp : (opOp C).Monoidal where
  ε' := 𝟙 _
  η' := 𝟙 _
  μ' X Y := 𝟙 _
  δ' X Y := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

instance monoidalUnopUnop : (unopUnop C).Monoidal where
  ε' := 𝟙 _
  η' := 𝟙 _
  μ' X Y := 𝟙 _
  δ' X Y := 𝟙 _
  ε_η := Category.comp_id _
  η_ε := Category.comp_id _
  μ_δ X Y := Category.comp_id _
  δ_μ X Y := Category.comp_id _

instance : (opOpEquivalence C).functor.Monoidal := monoidalUnopUnop
instance : (opOpEquivalence C).inverse.Monoidal := monoidalOpOp

@[simp] lemma opOp_ε : ε (opOp C) = 𝟙 (𝟙_ Cᵒᵖᵒᵖ) := rfl
@[simp] lemma opOp_η : η (opOp C) = 𝟙 _ := rfl
@[simp] lemma unopUnop_ε : ε (unopUnop C) = 𝟙 _ := rfl
@[simp] lemma unopUnop_η : η (unopUnop C) = 𝟙 _ := rfl
@[simp] lemma opOp_μ (X Y) : μ (opOp C) X Y = 𝟙 _ := rfl
@[simp] lemma opOp_δ (X Y) : δ (opOp C) X Y = 𝟙 _ := rfl
@[simp] lemma unopUnop_μ (X Y) : μ (unopUnop C) X Y = 𝟙 _ := rfl
@[simp] lemma unopUnop_δ (X Y) : δ (unopUnop C) X Y = 𝟙 _ := rfl

instance : (opOpEquivalence C).IsMonoidal where
  leftAdjoint_ε := by simp [Adjunction.homEquiv, opOpEquivalence]
  leftAdjoint_μ := by simp [Adjunction.homEquiv, opOpEquivalence]

end CategoryTheory
