module Utils.Misc where

open import Agda.Builtin.Equality

_∘_
  : ∀ {ℓ ℓ′ ℓ″}
    {a : Set ℓ}
    {b : @0 a → Set ℓ′}
    {c : {@0 x : a} → @0 b x → Set ℓ″}
    (g : {@0 x : a} (y : b x) → c y)
    (f : (x : a) → b x)
  → (x : a) → c (f x)
(g ∘ f) x = g (f x)
{-# COMPILE AGDA2HS _∘_ #-}

subst
  : ∀ {ℓ ℓ′} {@0 a : Set ℓ}
    (@0 f : @0 a → Set ℓ′)
    {@0 x y : a}
  → @0 x ≡ y → f x → f y
subst f refl x = x
{-# COMPILE AGDA2HS subst transparent #-}
