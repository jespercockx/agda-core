{-# OPTIONS --overlapping-instances #-}

open import Utils
open import Scope
open import ScopeImpl

Name = String

open IScope (simpleScope Name)

instance
  top : x ∈ (x ◃ α)
  top = here

  pop : {{x ∈ α}} → x ∈ (y ◃ α)
  pop {{p}} = there p

defs = ∅

cons = "true" ◃ "false" ◃ ∅

conArity : All (λ _ → Scope) cons
conArity = constAll ∅

open import Syntax (simpleScope Name) defs cons conArity
open import Reduce (simpleScope Name) defs cons conArity

`true : Term α
`true = con "true" (⇒weaken ⊆-∅)
`false : Term α
`false = con "false" (⇒weaken ⊆-∅)

∞ : ℕ
∞ = 9999999999999999

module Tests (@0 x y z : Name) where

  testTerm₁ : Term α
  testTerm₁ = apply (lam x (var x)) (sort (type 0))

  test₁ : reduce {α = ∅} ∞ testTerm₁ ≡ just (sort (type 0))
  test₁ = refl

  testTerm₂ : Term α
  testTerm₂ = let′ x `true (case x (branch "true" `false ∷ branch "false" `true ∷ []))

  test₂ : reduce {α = ∅} ∞ testTerm₂ ≡ just (con "false" _)
  test₂ = refl
