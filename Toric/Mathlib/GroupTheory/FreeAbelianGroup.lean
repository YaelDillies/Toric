import Mathlib.GroupTheory.FreeAbelianGroup

@[simps!]
def FreeAbelianGroup.liftAddEquiv {α G : Type*} [AddCommGroup G] :
    (α → G) ≃+ (FreeAbelianGroup α →+ G) :=
  ⟨lift, fun _ _ ↦ by ext; simp⟩
