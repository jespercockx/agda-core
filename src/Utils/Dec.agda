module Utils.Dec where

open import Haskell.Prelude hiding (Reflects; _∘_)
open import Agda.Primitive

@0 Reflects : ∀ {ℓ} → Set ℓ → Bool → Set ℓ
Reflects P True  = P
Reflects P False = P → ⊥

record ∃ {ℓ ℓ′} (@0 a : Set ℓ) (@0 P : a → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _⟨_⟩
  field
    value    : a
    @0 proof : P value
open ∃ public
{-# COMPILE AGDA2HS ∃ unboxed #-}

Dec : ∀ {ℓ} → @0 Set ℓ → Set ℓ
Dec P = ∃ Bool (Reflects P)
{-# COMPILE AGDA2HS Dec #-}

-- TODO(flupe): move upstream
_∘_
  : ∀ {ℓ ℓ′ ℓ″}
    {a : Set ℓ}
    {b : @0 a → Set ℓ′}
    {c : {@0 x : a} → @0 b x → Set ℓ″}
    (g : {@0 x : a} (y : b x) → c y)
    (f : (x : a) → b x)
  → (x : a) → c (f x)
(g ∘ f) x = g (f x)

mapDec : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′}
       → @0 (A → B)
       → @0 (B → A)
       → Dec A → Dec B
mapDec f g (True  ⟨ x ⟩) = True  ⟨ f x   ⟩
mapDec f g (False ⟨ h ⟩) = False ⟨ h ∘ g ⟩
{-# COMPILE AGDA2HS mapDec transparent #-}
