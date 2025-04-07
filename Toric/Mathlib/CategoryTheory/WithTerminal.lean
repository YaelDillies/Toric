import Mathlib.CategoryTheory.WithTerminal
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.Data.Fintype.Option

namespace CategoryTheory.WithTerminal

universe v u
variable {C : Type u} [Category.{v} C]

def OptionEquiv : Option C ≃ WithTerminal C where
  toFun
  | some a => of a
  | none => star
  invFun
  | of a => some a
  | star => none
  left_inv a := by cases a <;> simp
  right_inv a := by cases a <;> simp

instance instFinType [Fintype C] : Fintype (WithTerminal C) :=
  Fintype.ofEquiv (Option C) OptionEquiv

instance instFin [SmallCategory C] [FinCategory C] :
    FinCategory (WithTerminal C) where
  fintypeObj := inferInstance
  fintypeHom
  | star, star
  | of _, star => (inferInstance : Fintype PUnit)
  | star, of _ => (inferInstance : Fintype PEmpty)
  | of a, of b => (inferInstance : Fintype (a ⟶ b))

end CategoryTheory.WithTerminal
