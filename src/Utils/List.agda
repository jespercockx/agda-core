module Utils.List where

open import Haskell.Prelude hiding (All; a; b)
open import Agda.Primitive

{- NOTE(flupe):
     maybe we don't need this compiled to Haskell
     but this compiles to a list anyways
-}

private variable
  ℓ ℓ′ : Level
  a    : Set ℓ
  b    : @0 a → Set ℓ′
  x    : a
  xs   : List a

data All {a : Set ℓ} (b : @0 a → Set ℓ′) : @0 List a → Set (ℓ ⊔ ℓ′) where
  ANil  : All b []
  ACons : ∀ {@0 x xs} → b x → All b xs → All b (x ∷ xs)
{-# COMPILE AGDA2HS All #-}

data @0 _∈_ {a : Set ℓ} (@0 x : a) : List a → Set ℓ where
  here  : ∀ {@0 xs : List a} → x ∈ (x ∷ xs)
  there : ∀ {@0 y xs} → x ∈ xs → x ∈ (y ∷ xs)

@0 lookupAll : ∀ {@0 x xs} → All b xs → x ∈ xs → b x
lookupAll (ACons p _ ) (here) = p
lookupAll (ACons _ ps) (there i) = lookupAll ps i
