module Agda.Core.Utils where

record Sigma (a : Set) (p : @0 a → Set) : Set where
  constructor MkSigma
  field
    value : a
    proof : p value
open Sigma public
{-# COMPILE AGDA2HS Sigma #-}

pattern _⟨_⟩ a b = MkSigma a b

infix 4 Sigma
syntax Sigma a (λ x → p) = Σ[ x ∈ a ] p

Σ : (a : Set) (p : @0 a → Set) → Set
Σ = Sigma
{-# COMPILE AGDA2HS Σ inline #-}

infix 4 ∃
∃ : {a : Set} (p : @0 a → Set) → Set
∃ p = Sigma _ p
{-# COMPILE AGDA2HS ∃ inline #-}

syntax ∃ (λ x → p) = ∃[ x ] p
