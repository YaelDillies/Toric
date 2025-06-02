import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic.Spread

variable {M N₁ N₂ : Type*} [Monoid M] [CommMonoid N₁] [CommMonoid N₂]

/-- The monoid isomorphism `(M →* N₁) ≃* (M →* N₂)` obtained by postcomposition with
a multiplicative equivalence `e : N₁ ≃* N₂`. -/
@[to_additive "The monoid isomorphism `(M →+ N₁) ≃+ (M →+ N₂)` obtained by postcomposition with
an additive equivalence `e : N₁ ≃+ N₂`."]
def MonoidHom.postcompMulEquiv (e : N₁ ≃* N₂) : (M →* N₁) ≃* (M →* N₂) where
  __ := postcompEquiv e M
  map_mul' f g := by ext; exact map_mul e ..

/-- The monoid isomorphism `(M →* N₁) ≃* (M →* N₂)` obtained by postcomposition with
a multiplicative equivalence `e : N₁ ≃* N₂`. -/
@[to_additive "The monoid isomorphism `(M →+ N₁) ≃+ (M →+ N₂)` obtained by postcomposition with
an additive equivalence `e : N₁ ≃+ N₂`."]
def MonoidHom.precompMulEquiv {M N₁ N₂ : Type*} [CommMonoid M] [Monoid N₁] [Monoid N₂]
    (e : N₁ ≃* N₂) : (N₂ →* M) ≃* (N₁ →* M) where
  __ := precompEquiv e M
  map_mul' _ _ := rfl
