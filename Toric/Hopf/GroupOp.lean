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
      rintro (_|_)
      repeat
        ext
        exact a.w _
  }

@[simp]
def binaryCofanUnder.toPushoutCocone :
    BinaryCofan (Under.mk f) (Under.mk g) ⥤ PushoutCocone f g where
  obj c := PushoutCocone.mk c.inl.right c.inr.right (c.inl.w.symm.trans c.inr.w)
  map {c1 c2} a := {
    hom := a.hom.right
    w := by rintro (_|_|_) <;> simp [← Under.comp_right]
  }

lemma aux_left (c : BinaryCofan (Under.mk f) (Under.mk g)) {w : f ≫ c.inl.right = c.pt.hom} :
    (Under.homMk c.inl.right w) = c.inl := by
  ext
  simp

lemma aux_right {c : BinaryCofan (Under.mk f) (Under.mk g)} {w : g ≫ c.inr.right = c.pt.hom} :
    (Under.homMk c.inr.right w) = c.inr := by
  ext
  simp

def pushoutCoconeEquivBinaryCofan : PushoutCocone f g ≌ BinaryCofan (Under.mk f) (Under.mk g) :=
  .mk pushoutCocone.toBinaryCofan binaryCofanUnder.toPushoutCocone {
    hom.app c := c.eta.hom
    inv.app c := c.eta.inv
    inv.naturality {c1 c2} a := by ext; simp
  } {
    hom := {
      app c := (by
        dsimp
        sorry -- erw [aux_left c]
        ) ≫ (isoBinaryCofanMk c).inv
      naturality := sorry
    }
    inv := sorry
    hom_inv_id := sorry
    inv_hom_id := sorry
  }

def name (c : PushoutCocone f g)  (hc : IsColimit c) : IsColimit <|
    BinaryCofan.mk (Under.homMk (U := Under.mk f) c.inl rfl)
        (Under.homMk (U := Under.mk g) (V := Under.mk (f ≫ c.inl)) c.inr c.condition.symm) := sorry
  --BinaryCofan.isColimitMk _ _ _ _

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
