import Mathlib.CategoryTheory.Comma.Over.Basic

open CategoryTheory

variable {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} [IsIso f]

instance : (Over.map f).IsEquivalence :=
  inferInstanceAs <| (Over.mapIso <| asIso f).functor.IsEquivalence

instance : (Under.map f).IsEquivalence :=
  inferInstanceAs <| (Under.mapIso <| asIso f).functor.IsEquivalence
