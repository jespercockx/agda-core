module Agda.Core.Utils where

open import Haskell.Prelude
open import Haskell.Extra.Refinement using (∃; _⟨_⟩)  public
open import Haskell.Extra.Erase      using (Σ0; ⟨_⟩_) public

-- we have 3 kinds of dependent pairs available,
-- encoding (x : a) (y : p x)

-- ∃  from Haskell.Extra.Refinement, which erases the snd component
-- Σ0 from Haskell.Extra.Erasure,    which erases the fst component
-- Σ  from this module,              which keeps both components

record Σ (a : Set) (b : @0 a → Set) : Set where
  constructor _,_
  field
    fst : a
    snd : b fst
open Σ public
{-# COMPILE AGDA2HS Σ tuple #-}

-- we provide a shorthand syntax for all 3
------------------------------------------

infixr 2 ∃-syntax Σ Σ0-syntax

∃-syntax  = ∃
{-# COMPILE AGDA2HS ∃-syntax inline #-}

Σ0-syntax = Σ0
{-# COMPILE AGDA2HS Σ0-syntax inline #-}

syntax ∃-syntax  a (λ x → b) =  ∃[ x ∈ a ] b
syntax Σ0-syntax a (λ x → b) = Σ0[ x ∈ a ] b
syntax Σ         a (λ x → b) =  Σ[ x ∈ a ] b

pattern ∃⟨_⟩  x = x ⟨ _ ⟩
pattern Σ0⟨_⟩ x = ⟨ _ ⟩ x

map2 : {a : Set} {b c : @0 a → Set} (f : (@0 x : a) → b x → c x) → Σ a b →  Σ a c
map2 f (av , bv) = av , f av bv
{-# COMPILE AGDA2HS map2 #-}

data Fuel : Set where
  None : Fuel
  More : {{Fuel}} → Fuel
{-# COMPILE AGDA2HS Fuel #-}

witheq : (x : a) → ∃ a (λ y → x ≡ y)
witheq x = x ⟨ refl ⟩
{-# COMPILE AGDA2HS witheq transparent #-}

it : {{a}} → a
it {{x}} = x

record Instance (a : Set) : Set where
  constructor I
  field
    {{inst}} : a

{-# COMPILE AGDA2HS Instance unboxed #-}
