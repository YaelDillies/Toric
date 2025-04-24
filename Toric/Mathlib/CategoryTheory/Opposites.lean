import Mathlib.CategoryTheory.Opposites

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D}

/-- The opposite of a fully faithful functor is fully faithful. -/
protected def FullyFaithful.op (hF : F.FullyFaithful) : F.op.FullyFaithful where
  preimage {X Y} f := .op <| hF.preimage f.unop

/-- The opposite of a fully faithful functor is fully faithful. -/
protected def FullyFaithful.leftOp {F : C ⥤ Dᵒᵖ} (hF : F.FullyFaithful) :
    F.leftOp.FullyFaithful where
  preimage {X Y} f := .op <| hF.preimage f.op

/-- The opposite of a fully faithful functor is fully faithful. -/
protected def FullyFaithful.rightOp {F : Cᵒᵖ ⥤ D} (hF : F.FullyFaithful) :
    F.rightOp.FullyFaithful where
  preimage {X Y} f := .unop <| hF.preimage f.unop

end CategoryTheory.Functor
