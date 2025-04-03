import Mathlib.CategoryTheory.WithTerminal
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.Data.Fintype.Option


open CategoryTheory CategoryTheory.Limits CategoryTheory.WithTerminal

universe v u
variable {C : Type u} [Category.{v} C]

def OptionEquiv   : (Option C) ≃ (WithTerminal C) where
toFun
| some a => of a
| none => star
invFun
| of a => some a
| star => none
left_inv
| some _
| none => by simp
right_inv
| of _
| star => by simp

instance instFinType [Fintype C] : Fintype (WithTerminal C) :=
  Fintype.ofEquiv (Option C) OptionEquiv

instance instSmall  [SmallCategory C] :
SmallCategory (WithTerminal C) := inferInstance

instance instFin  [SmallCategory C] [FinCategory C] :
FinCategory (WithTerminal C) := {
  fintypeObj := inferInstance
  fintypeHom a b := match a, b with
  | star, star => (inferInstance : Fintype PUnit)
  | of _, star => (inferInstance : Fintype PUnit)
  | star, of _ => (inferInstance : Fintype PEmpty)
  | of a, of b => (inferInstance : Fintype (a ⟶ b))
}
