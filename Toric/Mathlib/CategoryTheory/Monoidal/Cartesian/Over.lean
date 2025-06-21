import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

open CategoryTheory MonoidalCategory Limits

attribute [local instance] Over.cartesianMonoidalCategory

@[reassoc (attr := simp)]
lemma CategoryTheory.Over.tensorHom_left_fst' {C : Type*} [Category C] [HasPullbacks C] {X : C}
    {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X) (f : R ⟶ mk fS) (g : T ⟶ mk fU) :
    (f ⊗ₘ g).left ≫ pullback.fst fS fU = pullback.fst R.hom T.hom ≫ f.left :=
  CategoryTheory.Over.tensorHom_left_fst ..

@[reassoc (attr := simp)]
lemma CategoryTheory.Over.tensorHom_left_snd' {C : Type*} [Category C] [HasPullbacks C] {X : C}
    {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X) (f : R ⟶ mk fS) (g : T ⟶ mk fU) :
    (f ⊗ₘ g).left ≫ pullback.snd fS fU = pullback.snd R.hom T.hom ≫ g.left :=
  CategoryTheory.Over.tensorHom_left_snd ..
