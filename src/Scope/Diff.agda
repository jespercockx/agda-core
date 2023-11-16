module Scope.Diff where

open import Haskell.Prelude

open import Utils.Erase
open import Scope.Core
open import Scope.Split
open import Scope.Sub
open import Scope.In

private variable
  @0 name : Set
  @0 x y : name
  @0 α α₁ α₂ β β₁ β₂ γ : Scope name

opaque
  unfolding Sub

  @0 diff : ∀ {α β : Scope name} → Sub α β → Scope name
  diff (⟨ p ⟩ _) = p

  diff-left : (p : α ⋈ β ≡ γ) → diff (subLeft p) ≡ β
  diff-left p = refl

  diff-right : (p : α ⋈ β ≡ γ) → diff (subRight p) ≡ α
  diff-right p = refl

  ⋈-diff : (p : α ⊆ β) → α ⋈ diff p ≡ β
  ⋈-diff = proj₂

  diff-⊆ : (p : α ⊆ β) → diff p ⊆ β
  diff-⊆ p = subRight (⋈-diff p)

  diff-case : (p : α ⊆ β) → In x β
            → (x ∈ α → a) → (x ∈ diff p → a) → a
  diff-case p = inSplitCase (⋈-diff p)

opaque
  unfolding diff

  diff-⊆-trans : (p : α ⊆ β) (q : β ⊆ γ) → diff p ⊆ diff (subTrans p q)
  diff-⊆-trans < p > < q > =
    let < _ , s > = splitAssoc p q
    in  < s >

diff-coerce : (p : α ⊆ β) (q : In x α) → diff q ⊆ diff (coerce p q)
diff-coerce p q = diff-⊆-trans q p