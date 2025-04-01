
/-
Copyright (c) 2025 Moisés Herradón Cueto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moisés Herradón Cueto
-/
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option

/-!
# Adding a final object to a category

We define the category `WithFinalObject`, which is obtained from a category of type `J` by
adjoining a new  element which is final, i.e. every object in `J` has a unique morphism to it.
-/

open CategoryTheory CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : Type w} [Category.{w'} J]

namespace CategoryTheory.Limits

/-- For any category `J`, `Option J` is a type that has one extra element, which
will be the final object (this is the same as `CategoryTheory.Limits.WidePullbackShape`)-/
def WithFinalObject (J : Type w) : Type w := Option J

namespace WithFinalObject

@[simps]
instance category : Category.{w'} (WithFinalObject J) where
  Hom a b:= match b with
  | none => PUnit
  | some b => match a with
    | none => PEmpty
    | some a => a ⟶ b

  id a := match a with
  | some a => 𝟙 a
  | none => PUnit.unit

  comp {a} {b} {c} f g := match a, b, c with
  | _, _, none => PUnit.unit
  | _, none, some _
  | none, some _, _ => by contradiction
  | some a, some b, some c => f ≫ g

  id_comp := fun {a} {b} f ↦
    match a, b with
    | _, none => by aesop
    | none, some b => by contradiction
    | some a, some b => Category.id_comp f

  comp_id := fun {a} {b} f ↦
    match a, b with
    | _, none => by aesop
    | none, some b => by contradiction
    | some a, some b => Category.comp_id f

  assoc := fun {a} {b} {c} {d} f g h ↦
    match a, b, c, d with
    | _, _, _, none => by aesop
    | _, _, none, some x
    | _, none, some x, _
    | none, some x, _, _ => by contradiction
    | some a, some b, some c, some d => Category.assoc f g h

  /-- The unique morphism from an element of the original category to the final object-/
  def term (a : J) : @Quiver.Hom (WithFinalObject J) _ (some a) none := PUnit.unit

  /-- The obvious inclusion of `J` into `WithFinalObject J`-/
  @[simps]
  def inclusion : J ⥤ WithFinalObject J := {
    obj := some
    map := id
  }

  instance IsFinType [Fintype J] : Fintype (WithFinalObject J) :=
    (inferInstance :  Fintype (Option J) )

  instance IsSmall  [SmallCategory J] :
  SmallCategory (WithFinalObject J) := inferInstance

  instance IsFin  [SmallCategory J] [FinCategory J] :
  FinCategory (WithFinalObject J) := {
    fintypeObj := inferInstance
    fintypeHom a b := match a, b with
    | _, none => (inferInstance : Fintype PUnit)
    | none, some _ => (inferInstance : Fintype PEmpty)
    | some a, some b => (inferInstance : Fintype (a ⟶ b))

  }

  /-- For any functor `K : J ⥤ Over X`, there is a canonical extension
  `WithFinalObject J ⥤ C`: it is defined as `K` on `J`, and it maps the final
  object to `X`-/
  @[simps]
  noncomputable def extendFunctor [h: HasTerminal C] (K : J ⥤ C):
    WithFinalObject J ⥤ C := {
    obj a := match a with
    | none => ⊤_ C
    | some a => K.obj a
    map {a} {b} f := match a, b with
    | _ , none => terminal.from _
    | none, some _ => by contradiction
    | some a, some b => K.map f
    map_comp {a} {b} {c} f g:=
    match a, b, c with
    | _, none, some _
    | none, some _, _ => by contradiction
    | _, none, none
    | some a, some b, none
    | some a, some b, some c => by aesop
  }


  /-- For any functor `K : J ⥤ Over X`, there is a canonical extension
  `WithFinalObject J ⥤ C`, since `Over X` has a final object, `𝟙 X`. It is
  easier to define it ad hoc, since the final object can be chosen canonically
  (note that any isomorphism mapping to `X` is also final)-/
  @[simps]
  def extendOver {X : C} (K : J ⥤ Over X) : WithFinalObject J ⥤ C := {
    obj a := match a with
    | none => X
    | some a => Comma.left (K.obj a)
    map {a} {b} f:= match a, b with
    | none, none => 𝟙 X
    | some a, none => (K.obj a).hom
    | none, some _ => by contradiction
    | some a, some b => CommaMorphism.left (K.map f)
    map_id a := by aesop
    map_comp {a} {b} {c} f g:=
    match a, b, c with
    | _, none, none
    | some a, some b, none => by aesop
    | _, none, some _
    | none, some _, _ => by contradiction
    | some a, some b, some c => by aesop
  }

  /-- The extension of a functor to over categories behaves well with compositions -/
  @[simps]
  def extendCompose {X : C} (K : J ⥤ Over X) (F : C ⥤ D) :
   (extendOver K ⋙ F) ≅ extendOver (K ⋙ (Over.post F)) := {
    hom := {
      app a := match a with
      | none => 𝟙 _
      | some a => 𝟙 _
      naturality {a} {b} f := match a, b with
      | _, none => by aesop
      | none, some _ => by contradiction
      | some a, some b => by simp
    }
    inv := {
      app a := match a with
      | none => 𝟙 _
      | some a => 𝟙 _
      naturality {a} {b} f := match a, b with
      | _, none => by aesop
      | none, some _ => by contradiction
      | some a, some b => by simp
    }
  }



  /-- Given a cone of a functor `J ⥤ Over X`, the same object essentially
  gives a cone of the extended functor `WithFinalObject J ⥤ C` -/
  @[simps]
  def coneToOver {X : C} {K : J ⥤ Over X} (t : Cone K) :
    Cone (extendOver K) := {
      pt := t.pt.left
      π := {
        app a := match a with
        | some a => CommaMorphism.left (t.π.app a)
        | none => t.pt.hom
        naturality a b f:=
        match a, b with
        | none , none
        | some a, none => by aesop
        | none, some _ => by contradiction
        | some a, some b => by
          have : (t.π.app b).left = (t.π.app a).left ≫ (K.map f).left := by
            calc
              (t.π.app b).left = (t.π.app a ≫ K.map f).left := by simp only [Functor.const_obj_obj,
                Cone.w]
              _ = (t.π.app a).left ≫ (K.map f).left := rfl
          simpa [Functor.const_obj_obj, Cone.w]
      }
    }

  /-- Given a functor `J ⥤ Over X` and a cone of its extension `WithFinalObject J ⥤ C`,
  the same object essentially gives a cone of the original functor-/
  @[simps]
  def coneFromOver {X : C} {K : J ⥤ Over X} (t : Cone (extendOver K)) : Cone K := {
    pt := Over.mk (t.π.app none)
    π := {
        app a := {
            left := t.π.app (some a)
            right := 𝟙 _
            w := by
              have := by
                calc
                  t.π.app (some a) ≫ (K.obj a).hom = t.π.app (some a)  ≫
                    (extendOver K).map (term a) := rfl
                  _ = t.π.app none := by simp only [Functor.const_obj_obj, Cone.w]
              simp [this]
        }
        naturality a b f := by
          ext
          let f₂ := inclusion.map f
          have eq_after_K: (K.map f₂).left =  (K.map f).left := by aesop
          have nat : t.π.app (some b) =
           t.π.app (some a) ≫ (K.map f₂).left := by simpa using t.π.naturality f₂
          simp [nat, eq_after_K]
    }
  }

  /-- Taking a cone in `Over X` to `C` and back to `Over X` is (isomorphic to) the identity -/
  def coneToFrom {X : C} {K : J ⥤ Over X} (t : Cone K) : coneFromOver (coneToOver t) ≅ t := {
    hom := {
      hom := 𝟙 t.pt
    }
    inv := {
      hom := 𝟙 t.pt
    }
  }


  /-- If a cone is the limit in `Over X`, then its extension to `C` is also the limit-/
  def limit_of_Over {X : C} {K : J ⥤ Over X} (lim : Cone K) (h : IsLimit lim) :
    IsLimit (coneToOver lim) := {
      lift t := (h.lift (coneFromOver t)).left
      fac s a := match a with
      | none => by aesop
      | some a => by
        calc
          (h.lift (coneFromOver s)).left ≫ (lim.π.app a).left =
           (h.lift (coneFromOver s) ≫ lim.π.app a).left := rfl
          _ = ((coneFromOver s).π.app a).left := by simp [ h.fac (coneFromOver s) a]
          _ = s.π.app (some a):= by simp
      uniq s f commutes := by
        change f = (h.lift (coneFromOver s)).left
        let f_over : (coneFromOver s).pt ⟶ lim.pt := Over.homMk f (commutes none)
        have := h.uniq (coneFromOver s) f_over ?_
        · calc
          f = f_over.left := rfl
          _ = (h.lift (coneFromOver s)).left := by rw [this]
        intro a
        ext
        calc
          (f_over ≫ lim.π.app a).left = f_over.left ≫ (lim.π.app a).left := rfl
          _ = f ≫ (lim.π.app a).left := by aesop
          _ = ((coneFromOver s).π.app a).left := commutes (some a)

    }

    /-- If a cone of an extended functor is the limit in `C`, then the corresponding
    cone in `Over X` is also the limit-/
    def limit_forget {X : C} {K : J ⥤ Over X} (lim : Cone (extendOver K)) (h : IsLimit lim) :
     IsLimit (coneFromOver lim) := {
      lift s :=
        @Over.homMk C _ X s.pt (coneFromOver lim).pt (h.lift (coneToOver s)) (by simp)
      uniq s f commutes := by
        change f = Over.homMk (h.lift (coneToOver s))
        have := h.uniq (coneToOver s) f.left ?_
        · ext ; simpa
        intro a
        cases a with
        | none => simpa using f.w
        | some a => simpa using (congrArg (Over.forget X).map (commutes a))
    }

end CategoryTheory.Limits.WithFinalObject
