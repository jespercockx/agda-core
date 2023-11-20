{-# OPTIONS --overlapping-instances #-}

module TestReduce where

open import Haskell.Prelude hiding (All)

open import Utils.Erase

open import Scope.Core
open import Scope.In
open import Scope.All
open import Scope.Split
open import Scope.Sub

name = String

private variable
  x y : name
  α : Scope name

instance
  top : In x (x ◃ α)
  top = inHere

  pop : {{x ∈ α}} → x ∈ (y ◃ α)
  pop {{p}} = inThere p

defs = mempty

cons = bind "true" $ bind "false" mempty

conArity : All (λ _ → Scope name) cons
conArity = allJoin (allSingl mempty) (allJoin (allSingl mempty) allEmpty)

open import Syntax defs cons conArity
open import Reduce defs cons conArity

opaque
  unfolding lookupAll inHere inThere splitRefl splitJoinRight subBindDrop subLeft

  `true : Term α
  `true = TCon "true" (inHere) SNil
  `false : Term α
  `false = TCon "false" (inThere inHere) SNil

∞ : Nat
∞ = 9999999999999999

module Tests (@0 x y z : name) where

  opaque
    unfolding step inBindCase inSplitCase inJoinCase `true `false decIn ∅-⋈-injective

    testTerm₁ : Term α
    testTerm₁ = apply (TLam x (TVar x inHere)) (TSort (STyp 0))

    test₁ : reduce {α = mempty} ∞ testTerm₁ ≡ Just (TSort (STyp 0))
    test₁ = refl

    testTerm₂ : Term α
    testTerm₂ = TApp `true (ECase (BBranch "true" inHere (rezz _) `false ∷ BBranch "false" (inThere inHere) (rezz _) `true ∷ []))

    test₂ : reduce {α = mempty} ∞ testTerm₂ ≡ Just `false
    test₂ = refl

-- -}