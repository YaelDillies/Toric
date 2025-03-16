import Mathlib.CategoryTheory.Opposites

namespace CategoryTheory.Equivalence
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

def leftOp (e : C ≌ Dᵒᵖ) : Cᵒᵖ ≌ D := e.op.trans (opOpEquivalence D)
def rightOp (e : Cᵒᵖ ≌ D) : C ≌ Dᵒᵖ := (opOpEquivalence C).symm.trans e.op

end CategoryTheory.Equivalence
