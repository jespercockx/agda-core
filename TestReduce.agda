{-# OPTIONS --overlapping-instances #-}

open import Utils

Name = String

open import Scope Name
open Variables

instance
  top : x ∈ (x ◃ α)
  top = here

  pop : {{x ∈ α}} → x ∈ (y ◃ α)
  pop {{p}} = there p

defs = ∅

cons = "true" ◃ "false" ◃ ∅

conArity : All (λ _ → Scope) cons
conArity = All<> (All[] ∅) (All<> (All[] ∅) All∅)

open import Syntax defs cons conArity
open import Reduce defs cons conArity

opaque
  unfolding lookupAll here there ⋈-refl ⋈-<>-right

  `true : Term α
  `true = con "true" []
  `false : Term α
  `false = con "false" []

∞ : ℕ
∞ = 9999999999999999

module Tests (@0 x y z : Name) where

  opaque
    unfolding step ◃-case ⋈-case `true `false _∈-≟_

    testTerm₁ : Term α
    testTerm₁ = apply (lam x (var x)) (sort (type 0))

    test₁ : reduce {α = ∅} ∞ testTerm₁ ≡ just (sort (type 0))
    test₁ = refl

    testTerm₂ : Term α
    testTerm₂ = appE `true (case (branch "true" `false ∷ branch "false" `true ∷ []) ∷ [])

    test₂ : reduce {α = ∅} ∞ testTerm₂ ≡ just `false
    test₂ = refl
