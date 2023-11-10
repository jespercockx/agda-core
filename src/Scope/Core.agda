module Scope.Core where

open import Haskell.Prelude hiding (All; _∘_)

open import Haskell.Law.Semigroup.Def using (IsLawfulSemigroup)
open import Haskell.Law.Semigroup.List using (iLawfulSemigroupList)
open import Haskell.Law.Monoid.Def using (IsLawfulMonoid)
open import Haskell.Law.Monoid.List using (iLawfulMonoidList)

open import Utils.Erase
open import Utils.Tactics
open import Utils.Dec as Dec
import Utils.List as List

private variable
  @0 name : Set

opaque
  Scope : (@0 name : Set) → Set
  Scope name = List (Erase name)
  {-# COMPILE AGDA2HS Scope #-}

  singleton : @0 name → Scope name
  singleton x = Erased x ∷ []
  {-# COMPILE AGDA2HS singleton #-}

  syntax singleton x = [ x ]

  instance
    iSemigroupScope : Semigroup (Scope name)
    iSemigroupScope = iSemigroupList

    iMonoidScope : Monoid (Scope name)
    iMonoidScope = iMonoidList

    iLawfulSemigroupScope : IsLawfulSemigroup (Scope name)
    iLawfulSemigroupScope = iLawfulSemigroupList

    iLawfulMonoidScope : IsLawfulMonoid (Scope name)
    iLawfulMonoidScope = iLawfulMonoidList

opaque
  bind : @0 name → Scope name → Scope name
  bind x α = singleton x <> α
  {-# COMPILE AGDA2HS bind #-}

  syntax bind x α = x ◃ α

opaque
  unfolding Scope bind

  rezzBind
    : {@0 α : Scope name} {@0 x : name}
    → Rezz _ α → Rezz _ (bind x α)
  rezzBind = rezzCong2 _∷_ rezzErase
  {-# COMPILE AGDA2HS rezzBind #-}
