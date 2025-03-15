/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.Algebra.Category.HopfAlgebraCat.Basic
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Toric.Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# The equivalence between Hopf algebras and cogroup algebras
-/

open CategoryTheory Opposite Limits

variable {R : Type*} [CommRing R]

noncomputable instance : ChosenFiniteProducts (Under <| CommRingCat.of R)ᵒᵖ where
  product X Y := {
    cone :=
      let _ : Algebra R (unop X).right := X.1.hom.hom.toAlgebra
      let _ : Algebra R (unop Y).right := Y.1.hom.hom.toAlgebra
      BinaryCofan.op <| pushoutCocone.toBinaryCofan.obj <| CommRingCat.pushoutCocone R
        (unop X).right (unop Y).right
    isLimit :=
      let _ : Algebra R (unop X).right := X.1.hom.hom.toAlgebra
      let _ : Algebra R (unop Y).right := Y.1.hom.hom.toAlgebra
      BinaryCofan.IsColimit.op <| pushoutCocone.IsColimit.toBinaryCofanIsColimit <|
        CommRingCat.pushoutCoconeIsColimit R _ _
  }
  terminal := ⟨_, terminalOpOfInitial Under.mkIdInitial⟩

variable (R) in
def hopfAlgebraCatEquivGrp : (HopfAlgebraCat R)ᵒᵖ ≌ Grp_ (Under <| CommRingCat.of R)ᵒᵖ := sorry
