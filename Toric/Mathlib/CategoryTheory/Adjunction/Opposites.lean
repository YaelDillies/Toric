import Mathlib.CategoryTheory.Adjunction.Opposites

namespace CategoryTheory
variable {C D : Type*} [Category C] [Category D]

instance {F : C ⥤ D} [F.IsLeftAdjoint] : F.op.IsRightAdjoint :=
  ⟨F.rightAdjoint.op, ⟨.op <| .ofIsLeftAdjoint _⟩⟩

instance {F : C ⥤ D} [F.IsRightAdjoint] : F.op.IsLeftAdjoint :=
  ⟨F.leftAdjoint.op, ⟨.op <| .ofIsRightAdjoint _⟩⟩

instance {F : C ⥤ Dᵒᵖ} [F.IsLeftAdjoint] : F.leftOp.IsRightAdjoint :=
  ⟨F.rightAdjoint.rightOp, ⟨.leftOp <| .ofIsLeftAdjoint _⟩⟩

-- TODO: Do we need to introduce `Adjunction.leftUnop`?
instance {F : C ⥤ Dᵒᵖ} [F.IsRightAdjoint] : F.leftOp.IsLeftAdjoint := by
  have adj := Adjunction.ofIsRightAdjoint F
  refine ⟨F.leftAdjoint.rightOp, ⟨NatTrans.op adj.counit, NatTrans.unop adj.unit, ?_, ?_⟩⟩
  · rintro X
    refine Quiver.Hom.op_inj ?_
    simp
  · rintro Y
    refine Quiver.Hom.unop_inj ?_
    simp

-- TODO: Do we need to introduce `Adjunction.rightUnop`?
instance {F : Cᵒᵖ ⥤ D} [F.IsLeftAdjoint] : F.rightOp.IsRightAdjoint := by
  have adj := Adjunction.ofIsLeftAdjoint F
  refine ⟨F.rightAdjoint.leftOp, ⟨NatTrans.op adj.counit, NatTrans.unop adj.unit, ?_, ?_⟩⟩
  · rintro X
    refine Quiver.Hom.op_inj ?_
    simp
  · rintro Y
    refine Quiver.Hom.unop_inj ?_
    simp

-- TODO: Do we need to introduce `Adjunction.leftOp`/`Adjunction.rightUnop`
instance {F : Cᵒᵖ ⥤ D} [F.IsRightAdjoint] : F.rightOp.IsLeftAdjoint :=
  ⟨F.leftAdjoint.leftOp, ⟨.rightOp <| .ofIsRightAdjoint _⟩⟩

end CategoryTheory
