import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory Opposite Limits

namespace CategoryTheory.Limits
variable {C : Type*} [Category C] {X Y P : C}

@[simps!]
def BinaryCofan.op (c : BinaryCofan X Y) : BinaryFan (.op X : Cᵒᵖ) (.op Y) :=
  .mk (.op c.inl) (.op c.inr)

@[simps!]
def BinaryFan.unop (c : BinaryFan (.op X : Cᵒᵖ) (.op Y)) : BinaryCofan X Y :=
  BinaryCofan.mk c.fst.unop c.snd.unop

@[simp] lemma BinaryCofan.op_mk (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : op (mk ι₁ ι₂) = .mk ι₁.op ι₂.op := rfl

@[simp] lemma BinaryFan.unop_mk (ι₁ : op P ⟶ op X) (ι₂ : op P ⟶ op Y) :
    unop (mk ι₁ ι₂) = .mk ι₁.unop ι₂.unop := rfl

lemma aux {D : Type*} [Category D] {F G : C ⥤ D} (α : F ⟶ G) :
    (NatTrans.op α).app (.op X) = (α.app X).op := rfl

def BinaryCofan.IsColimit.op {c : BinaryCofan X Y} (hc : IsColimit c) : IsLimit <| c.op where
  lift s := .op <| hc.desc (BinaryFan.unop s)
  fac s := by rintro (_|_) <;> simp [← CategoryTheory.op_comp, hc.fac]
  uniq s m h := by
    replace h j : c.ι.app j ≫ m.unop = (BinaryFan.unop s).ι.app j := by
      specialize h j; obtain ⟨_ | _⟩ := j <;> simpa using Quiver.Hom.op_inj h
    simpa using congr($(hc.uniq (BinaryFan.unop s) m.unop h).op)

end CategoryTheory.Limits
