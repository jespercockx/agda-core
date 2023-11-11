module Scope.In where

open import Haskell.Prelude

open import Utils.Erase

open import Scope.Core
open import Scope.Split
open import Scope.Sub

private variable
  @0 name : Set
  @0 x y : name
  @0 α β γ : Scope name

opaque
  In : @0 name → @0 Scope name → Set
  In x α = singleton x ⊆ α
  {-# COMPILE AGDA2HS In #-}

syntax In x α = x ∈ α

opaque
  unfolding In

  coerce : α ⊆ β → x ∈ α → x ∈ β
  coerce p q = subTrans q p
  {-# COMPILE AGDA2HS coerce #-}

opaque
  unfolding In bind

  inHere : x ∈ (x ◃ α)
  inHere {x = x} = subLeft (splitRefl (rezz [ x ]))
  {-# COMPILE AGDA2HS inHere #-}

  inThere : x ∈ α → x ∈ (y ◃ α)
  inThere = subBindDrop
  {-# COMPILE AGDA2HS inThere #-}

  bindSubToIn : (x ◃ α) ⊆ β → x ∈ β
  bindSubToIn {x = x} = joinSubLeft (rezz ([ x ]))
  {-# COMPILE AGDA2HS bindSubToIn #-}

opaque
  unfolding In Split Sub bind

  @0 inEmptyToBot : x ∈ mempty → ⊥
  inEmptyToBot ()

  inEmptyCase : @0 (x ∈ mempty) → a
  inEmptyCase p = error {i = inEmptyToBot p} "impossible"
  {-# COMPILE AGDA2HS inEmptyCase #-}

  inSingCase : x ∈ [ y ] → (@0 x ≡ y → a) → a
  inSingCase < EmptyR    > f = f refl
  inSingCase < ConsL _ _ > f = f refl
  {-# COMPILE AGDA2HS inSingCase #-}

  inSplitCase : α ⋈ β ≡ γ → x ∈ γ → (x ∈ α → a) → (x ∈ β → a) → a
  inSplitCase EmptyL      < EmptyR     > f g = g inHere
  inSplitCase EmptyL      < ConsL x q  > f g = g inHere
  inSplitCase EmptyL      < ConsR x q  > f g = g (inThere < q >)
  inSplitCase EmptyR      < EmptyR     > f g = f inHere
  inSplitCase EmptyR      < ConsL x q  > f g = f inHere
  inSplitCase EmptyR      < ConsR x q  > f g = f (inThere < q >)
  inSplitCase (ConsL x p) < EmptyR     > f g = f inHere
  inSplitCase (ConsL x p) < ConsL .x q > f g = f inHere
  inSplitCase (ConsL x p) < ConsR .x q > f g = inSplitCase p < q > (f ∘ inThere) g
  inSplitCase (ConsR x p) < EmptyR     > f g = g inHere
  inSplitCase (ConsR x p) < ConsL .x q > f g = g inHere
  inSplitCase (ConsR x p) < ConsR .x q > f g = inSplitCase p < q > f (g ∘ inThere)
  {-# COMPILE AGDA2HS inSplitCase #-}

opaque
  inJoinCase
    : Rezz _ α
    → x ∈ (α <> β) → (x ∈ α → a) → (x ∈ β → a) → a
  inJoinCase r = inSplitCase (splitRefl r)
  {-# COMPILE AGDA2HS inJoinCase #-}

opaque
  unfolding Scope Sub bind

  inBindCase : x ∈ (y ◃ α) → (@0 x ≡ y → a) → (x ∈ α → a) → a
  inBindCase {y = y} p f g = inJoinCase (rezz [ y ]) p (λ q → (inSingCase q f)) g
  {-# COMPILE AGDA2HS inBindCase #-}
