import Mathlib
import Toric.Mathlib.CategoryTheory.ChosenFiniteProducts.Over

open CategoryTheory Opposite Limits

section

variable {C : Type*} [Category C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}

@[simp]
def pushoutCocone.toBinaryCofan : PushoutCocone f g ⥤ BinaryCofan (Under.mk f) (Under.mk g) where
  obj c := BinaryCofan.mk (Under.homMk (U := Under.mk f) c.inl rfl)
      (Under.homMk (U := Under.mk g) (V := Under.mk (f ≫ c.inl)) c.inr c.condition.symm)
  map {c1 c2} a := {
    hom := Under.homMk a.hom
    w := by
      rintro (_|_) <;> aesop_cat
  }

@[simp]
def binaryCofanUnder.toPushoutCocone :
    BinaryCofan (Under.mk f) (Under.mk g) ⥤ PushoutCocone f g where
  obj c := PushoutCocone.mk c.inl.right c.inr.right (c.inl.w.symm.trans c.inr.w)
  map {c1 c2} a := {
    hom := a.hom.right
    w := by rintro (_|_|_) <;> simp [← Under.comp_right]
  }

def aux_unit :
    𝟭 (PushoutCocone f g) ≅ pushoutCocone.toBinaryCofan ⋙ binaryCofanUnder.toPushoutCocone :=
  NatIso.ofComponents (fun c ↦ c.eta) (by aesop_cat)

def aux_counit :
    binaryCofanUnder.toPushoutCocone ⋙ pushoutCocone.toBinaryCofan
    ≅ 𝟭 (BinaryCofan (Under.mk f) (Under.mk g)) :=
  NatIso.ofComponents (fun X ↦ Limits.BinaryCofan.ext (Under.isoMk (Iso.refl _)
    (by simpa using X.inl.w.symm)) (by aesop_cat) (by aesop_cat))
    (by intros; ext; simp [BinaryCofan.ext])

@[simp]
def pushoutCoconeEquivBinaryCofan : PushoutCocone f g ≌ BinaryCofan (Under.mk f) (Under.mk g) :=
  .mk pushoutCocone.toBinaryCofan binaryCofanUnder.toPushoutCocone aux_unit aux_counit

def pushoutCocone.IsColimit.toBinaryCofanIsColimit (c : PushoutCocone f g)  (hc : IsColimit c) :
    IsColimit <| pushoutCocone.toBinaryCofan.obj c :=
  (IsColimit.ofCoconeEquiv pushoutCoconeEquivBinaryCofan).symm hc

end

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {X Y P : C}

@[simp]
def BinaryCofan.op (c : BinaryCofan X Y) : BinaryFan (.op X : Cᵒᵖ) (.op Y) :=
  BinaryFan.mk (.op c.inl) (.op c.inr)

@[simp]
def BinaryFan.unop (c : BinaryFan (.op X : Cᵒᵖ) (.op Y)) : BinaryCofan X Y :=
  BinaryCofan.mk c.fst.unop c.snd.unop

@[simp]
lemma BinaryCofan.op_mk  (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
    BinaryCofan.op (.mk ι₁ ι₂) = .mk ι₁.op ι₂.op := rfl

lemma aux {D : Type*} [Category D] {F G : C ⥤ D} (α : F ⟶ G) :
    (NatTrans.op α).app (.op X) = (α.app X).op := rfl

def BinaryCofan.IsColimit.op {c : BinaryCofan X Y} (hc : IsColimit c) : IsLimit <| c.op where
  lift s := .op <| hc.desc (BinaryFan.unop s)
  fac s := by rintro (_|_) <;> simp [← CategoryTheory.op_comp, hc.fac]
  uniq s m h := by
    have := hc.uniq (BinaryFan.unop s) m.unop fun j ↦ by
      refine Quiver.Hom.op_inj ?_
      simp
      have := h j
      --simpa [← NatTrans.op_app, ← aux] using this
      sorry
    sorry


end CategoryTheory.Limits
section
universe u v

variable {R : Type u} [CommRing R]

--TODO
noncomputable instance : ChosenFiniteProducts (Under <| CommRingCat.of R)ᵒᵖ where
  product X Y := {
    cone :=
      let _ : Algebra R (unop X).right := X.1.hom.hom.toAlgebra
      let _ : Algebra R (unop Y).right := Y.1.hom.hom.toAlgebra
      BinaryCofan.op <| pushoutCocone.toBinaryCofan.obj <| CommRingCat.pushoutCocone R
        (unop X).right (unop Y).right
    isLimit := sorry
  }
  terminal := ⟨_, terminalOpOfInitial Under.mkIdInitial⟩


variable (R)
def HopfAlgebra.equivGrp : (HopfAlgebraCat.{u} R)ᵒᵖ ≌ Grp_ <| (Under <| CommRingCat.of R)ᵒᵖ := sorry

end
