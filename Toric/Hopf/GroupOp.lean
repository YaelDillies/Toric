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
  .ofCoconeEquiv pushoutCoconeEquivBinaryCofan.symm (.ofIsoColimit hc (by simp; exact c.eta))

end

section
universe u v

variable {R : Type u} [CommRing R]

noncomputable instance : ChosenFiniteProducts (Under <| CommRingCat.of R)ᵒᵖ where
  product X Y := sorry
  terminal := ⟨_, terminalOpOfInitial Under.mkIdInitial⟩


variable (R)
def HopfAlgebra.equivGrp : HopfAlgebraCat.{u} R ≌ Grp_ <| (Under <| CommRingCat.of R)ᵒᵖ := sorry

end
