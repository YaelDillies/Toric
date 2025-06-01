import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Grp_

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme
universe u
variable {M S T : Scheme.{u}} [M.Over S] {f : T ⟶ S}

instance : (Over.pullback f).Braided := .ofChosenFiniteProducts _

instance canonicallyOverPullback : (pullback (M ↘ S) f).CanonicallyOver T where
  hom := pullback.snd (M ↘ S) f

instance mon_ClassAsOverPullback [Mon_Class (asOver M S)] :
    Mon_Class (asOver (pullback (M ↘ S) f) T) :=
  ((Over.pullback f).mapMon.obj <| .mk' <| asOver M S).instMon_ClassX

instance isCommMon_asOver_pullback [Mon_Class (asOver M S)] [IsCommMon (asOver M S)] :
    IsCommMon (asOver (pullback (M ↘ S) f) T) :=
  ((Over.pullback f).mapCommMon.obj <| .mk' <| asOver M S).instIsCommMonX

instance Grp_ClassAsOverPullback [Grp_Class (asOver M S)] :
    Grp_Class (asOver (pullback (M ↘ S) f) T) :=
  ((Over.pullback f).mapGrp.obj <| .mk' <| asOver M S).instGrp_ClassX

end AlgebraicGeometry.Scheme
