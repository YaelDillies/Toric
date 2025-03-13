/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.GroupScheme.SchemeOver

open CategoryTheory AlgebraicGeometry

universe u

section
variable {C A : Type*} [Category C] [ChosenFiniteProducts C]
    {R : CommRingCat} [CommGroup A]

instance :
    Grp_Class <| Over.mk <| Spec.map <| CommRingCat.ofHom <| algebraMap R <| MonoidAlgebra R A :=
  sorry

end

namespace AlgebraicGeometry.Scheme
variable  {R : CommRingCat.{u}} {G : Over (Spec R)} [Grp_Class G]
    {A : Type u} [CommGroup A] [Monoid.FG A]

variable (G) in
class IsDiagonalisable : Prop where
  existsIso :
    ∃ (A : Type u) (_ : CommGroup A) (_ : Monoid.FG A),
      Nonempty <| Grp_.mk' G ≅ sorry
      -- Grp_.mk' <| .mk <| Spec.map <| CommRingCat.ofHom <| algebraMap R <| MonoidAlgebra R A

instance :
    IsDiagonalisable <| .mk <| Spec.map <| CommRingCat.ofHom <| algebraMap R <| MonoidAlgebra R A :=
  ⟨⟨A, _, ‹_›, sorry⟩⟩

end AlgebraicGeometry.Scheme
