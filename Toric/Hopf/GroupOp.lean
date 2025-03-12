import Mathlib
import Toric.Mathlib.CategoryTheory.ChosenFiniteProducts.Over

open CategoryTheory Opposite Limits

section

variable {C : Type*} [Category C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}

def pushoutCoconeEquivBinaryCofan : PushoutCocone f g ≌ BinaryCofan (Under.mk f) (Under.mk g) where
  functor := {
    obj c := BinaryCofan.mk (Under.homMk (U := Under.mk f) c.inl rfl)
        (Under.homMk (U := Under.mk g) (V := Under.mk (f ≫ c.inl)) c.inr c.condition.symm)
    map {c1 c2} a := {
      hom := Under.homMk a.hom
      w := by
        rintro ⟨(_|_)⟩
        repeat
          ext
          exact a.w _
    }
  }
  inverse := {
    obj c := PushoutCocone.mk c.inl.right c.inr.right (c.inl.w.symm.trans c.inr.w)
    map {c1 c2} a := {
      hom := a.hom.right
      w := by rintro (_|_|_) <;> simp [← Under.comp_right]
    }
  }
  unitIso := {
    hom := {
      app c := c.eta.hom
      naturality {c1 c2} a := sorry --by ext; simp -- removable
    }
    inv := {
      app c := c.eta.inv
      naturality {c1 c2} a := sorry  -- by ext; simp
    }
    hom_inv_id := sorry
    inv_hom_id := sorry
  }
  counitIso := sorry
  functor_unitIso_comp := sorry

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
