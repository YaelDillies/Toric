import Mathlib
import Toric.Hopf.MonoidAlgebra

variable {G H k : Type*} [Group G] [Group H] [Field k]

open Coalgebra in
noncomputable
def MonoidAlgebra.hopfToGroup (f : MonoidAlgebra k G →ₐc[k] MonoidAlgebra k H) : G → H := by
  intro g
  have : IsGroupLikeElem k (MonoidAlgebra.of k G g) := isGroupLikeElem_of g
  have : IsGroupLikeElem k (f (.of k G g)) := by
    exact IsGroupLikeElem.map f this
  simp at this
  exact Exists.choose this

noncomputable
def MonoidAlgebra.homEquivHopfHom : (MonoidAlgebra k G →ₐc[k] MonoidAlgebra k H) ≃ (G → H) where
  toFun f := MonoidAlgebra.hopfToGroup f
  invFun f := sorry
  left_inv := sorry
  right_inv := sorry
