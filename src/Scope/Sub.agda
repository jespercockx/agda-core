module Scope.Sub where

open import Haskell.Prelude

open import Utils.Erase
open import Scope.Core
open import Scope.Split

private variable
  @0 name  : Set
  @0 x     : name
  @0 α β γ : Scope name

opaque
  Sub : (@0 α β  : Scope name) → Set
  Sub α β = Σ0 _ (λ γ → α ⋈ γ ≡ β)
  {-# COMPILE AGDA2HS Sub #-}

  syntax Sub α β = α ⊆ β

  subTrans : α ⊆ β → β ⊆ γ → α ⊆ γ
  subTrans < p > < q > =
    let < r , _ > = splitAssoc p q
    in  < r >
  {-# COMPILE AGDA2HS subTrans #-}

  subLeft : α ⋈ β ≡ γ → α ⊆ γ
  subLeft p = < p >
  {-# COMPILE AGDA2HS subLeft transparent #-}

  subRight : α ⋈ β ≡ γ → β ⊆ γ
  subRight p = < splitComm p >
  {-# COMPILE AGDA2HS subRight #-}

  subWeaken : α ⊆ β → α ⊆ (bind x β)
  subWeaken < p > = < splitBindRight p >
  {-# COMPILE AGDA2HS subWeaken #-}

  subEmpty : mempty ⊆ α
  subEmpty = subLeft splitEmptyLeft
  {-# COMPILE AGDA2HS subEmpty #-}

  subRefl : α ⊆ α
  subRefl = subLeft splitEmptyRight
  {-# COMPILE AGDA2HS subRefl #-}
