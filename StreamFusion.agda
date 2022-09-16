open import Haskell.Prelude
open import Haskell.Prim.Thunk

variable @0 i : Size

record Stream (a : Set) (@0 i : Size) : Set where
  pattern; inductive; constructor _:>_
  field
    shead : a
    stail : Thunk (Stream a) i
open Stream public

{-# COMPILE AGDA2HS Stream #-}

smap : (a → b) → Stream a i → Stream b i
smap f (x :> xs) = (f x) :> (λ where .force → smap f (force xs))

{-# COMPILE AGDA2HS smap #-}

record Bisim (i : Size) (s₁ s₂ : Stream a i)  : Set where
  coinductive
  field
    shead : shead s₁ ≡ shead s₂
    stail : ∀ {j : Size< i} → Bisim j (force (stail s₁)) (force (stail s₂))
open Bisim public

syntax Bisim i s₁ s₂ = s₁ ≈[ i ] s₂

smap-fusion : (f : a → b) (g : b → c) (s : Stream a i)
            → smap {i = i} g (smap {i = i} f s) ≈[ i ] smap {i = i} (g ∘ f) s
smap-fusion f g (hd :> tl) .shead = refl
smap-fusion f g (hd :> tl) .stail = smap-fusion f g (tl .force)
