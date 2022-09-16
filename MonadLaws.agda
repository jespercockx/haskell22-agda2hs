open import Haskell.Prelude

record VerifiedMonad (m : Set → Set) {{iMonad : Monad m}} : Set₁ where
  field
    left-id  : ∀ {a b} (x : a) (f : a → m b)
             → (return x >>= f) ≡ f x
    right-id : ∀ {a} (k : m a)
             → (k >>= return) ≡ k
    assoc    : ∀ {a b c} (k : m a) (f : a → m b) (g : b → m c)
             → ((k >>= f) >>= g) ≡ (k >>= (λ x → f x >>= g))
open VerifiedMonad

instance
  _ : VerifiedMonad Maybe
  _ = λ where
    .left-id → λ x f → refl
    .right-id Nothing → refl
    .right-id (Just x) → refl
    .assoc Nothing f g → refl
    .assoc (Just x) f g → refl

instance
  _ : {r : Set} → VerifiedMonad (λ a → (r → a))
  _ = λ where
    .left-id → λ x f → refl
    .right-id → λ k → refl
    .assoc → λ k f g → refl
