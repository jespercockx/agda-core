-- An abstract interface to representations of scopes

{- Design constraints:
- Abstract interface for working with scopes
- Well-scoped syntax
- Scopes are runtime-irrelevant
- Joining two scopes α and β should only increase the size of the indices by a constant
- Possibility to construct from a proof of x ∈ α a "remainder scope" α' with x removed
- Empty scopes should not matter (see below)
- Variable indices are somehow bounded in size by the size of the scope
  (todo: add a proper notion of "size" to the interface?)
-}

{- Problem: should empty scopes matter?

We say that "empty scopes matter" if the following are NOT all equivalent:
- α ⋈ β ≡ γ
- (∅ <> α) ⋈ β ≡ γ
- (α <> ∅) ⋈ β ≡ γ
- α ⋈ (∅ <> β) ≡ γ
- α ⋈ (β <> ∅) ≡ γ
- α ⋈ β ≡ (∅ <> γ)
- α ⋈ β ≡ (γ <> ∅)

It is clearly desirable to have empty scopes not matter, but designing a
concrete implementation that satisfies this (as well as the other properties
above) is challenging.

-}

{-# OPTIONS --no-forcing #-} -- temporary until #6867 is fixed

-- open import Utils
open import Haskell.Prelude hiding (All; _∘_)
open import Haskell.Law.Equality
import Haskell.Law.List as List

open import Utils.Erase
open import Utils.Tactics
open import Utils.Dec as Dec
import Utils.List as List

module Scope where

  ----------------------------

  @0 <>-∅ : {α : Scope name} → α <> empty ≡ α
  <>-∅ = List.++-[] _

  @0 ∅-<> : {α : Scope name} → empty <> α ≡ α
  ∅-<> = refl

  @0 <>-assoc : {α β γ : Scope name} → (α <> β) <> γ ≡ α <> (β <> γ)
  <>-assoc {α = []} = refl
  <>-assoc {α = x ∷ α} = cong (x ∷_) (<>-assoc {α = α})

  ---------------------------


opaque
  unfolding Split



-- {-# COMPILE AGDA2HS _!!!_ #-}

opaque
  unfolding Split Sub

  -- TODO(flupe): Use Eq and LawfulEq
  decSplit : {@0 α β γ : Scope name} → (p q : α ⋈ β ≡ γ) → Dec (p ≡ q)
  decSplit (EmptyL   ) (EmptyL   ) = True ⟨ refl ⟩
  decSplit (EmptyR   ) (EmptyR   ) = True ⟨ refl ⟩
  decSplit (ConsL x p) (ConsL x q) = mapDec (cong (ConsL x)) (λ where refl → refl) (decSplit p q)
  decSplit (ConsR x p) (ConsR x q) = mapDec (cong (ConsR x)) (λ where refl → refl) (decSplit p q)
  decSplit (EmptyL   ) (EmptyR   ) = False ⟨ (λ ()) ⟩
  decSplit (EmptyL   ) (ConsR y q) = False ⟨ (λ ()) ⟩
  decSplit (EmptyR   ) (EmptyL   ) = False ⟨ (λ ()) ⟩ 
  decSplit (EmptyR   ) (ConsL x q) = False ⟨ (λ ()) ⟩ 
  decSplit (ConsL x p) (EmptyR   ) = False ⟨ (λ ()) ⟩ 
  decSplit (ConsL x p) (ConsR x q) = False ⟨ (λ ()) ⟩ 
  decSplit (ConsR x p) (EmptyL   ) = False ⟨ (λ ()) ⟩ 
  decSplit (ConsR x p) (ConsL x q) = False ⟨ (λ ()) ⟩ 

  syntax decSplit p q = p ⋈-≟ q

  private
    @0 ∅-⋈-injective : {@0 α β : Scope name} → empty ⋈ α ≡ β → α ≡ β
    ∅-⋈-injective EmptyL = refl
    ∅-⋈-injective EmptyR = refl
    ∅-⋈-injective (ConsR x p) rewrite ∅-⋈-injective p = refl

    J : {@0 a : Set} {@0 x : a} (@0 ϕ : (@0 y : a) → @0 x ≡ y → Set)
      → ϕ x refl
      → ∀ {@0 y} (@0 p : x ≡ y)
      → ϕ y p
    J ϕ z refl = z
    {-# COMPILE AGDA2HS J transparent #-}

  _∈-≟_ : {@0 α : Scope name} {@0 x y : name} (p : x ∈ α) (q : y ∈ α)
    → Dec (_≡_ {A = Σ0 name (λ n → n ∈ α)} (⟨ x ⟩ p) (⟨ y ⟩ q))
  < EmptyR    > ∈-≟ < EmptyR    > = True  ⟨ refl   ⟩
  < EmptyR    > ∈-≟ < ConsL x q > = False ⟨ (λ ()) ⟩
  < ConsL x p > ∈-≟ < EmptyR    > = False ⟨ (λ ()) ⟩
  < ConsL x p > ∈-≟ < ConsL x q > = 
    J (λ q _ → Dec (_≡_ {A = Σ0 _ (λ n → n ∈ _)} (⟨ x ⟩ ⟨ _ ⟩ ConsL x p) (⟨ x ⟩ ⟨ _ ⟩ ConsL x {!!})))
      (mapDec (cong (λ r → ⟨ _ ⟩ ⟨ _ ⟩ ConsL x r))
             (λ where refl → refl)
             (p ⋈-≟ q))
      (trans (∅-⋈-injective p) (sym (∅-⋈-injective q)))
    -- case trans (∅-⋈-injective p) (sym (∅-⋈-injective q)) of λ where
    --   refl → mapDec (cong (λ r → ⟨ _ ⟩ ⟨ _ ⟩ ConsL x r))
    --                 (λ where refl → refl)
    --                 (p ⋈-≟ q)
  < ConsL x p > ∈-≟ < ConsR x q > = False ⟨ (λ ()) ⟩
  < ConsR x p > ∈-≟ < ConsL x q > = False ⟨ (λ ()) ⟩
  < ConsR x p > ∈-≟ < ConsR x q > = mapDec aux (λ where refl → refl) (< p > ∈-≟ < q >)
    where
      aux : ∀ {@0 x y z α β γ} {p : Join [ x ] α γ} {q : Join [ y ] β γ} →
            _≡_ {A = Σ0 name (λ n → n ∈ γ)} (⟨ x ⟩ ⟨ α ⟩ p) (⟨ y ⟩ ⟨ β ⟩ q) →
            _≡_ {A = Σ0 name (λ n → n ∈ (Erased z ∷ γ))}
               (⟨ x ⟩ ⟨ Erased z ∷ α ⟩ ConsR z p)
               (⟨ y ⟩ ⟨ Erased z ∷ β ⟩ ConsR z q)
      aux refl = refl

{-
  -- TODO: clean up this horrible mess of a definition

_≟_ : (@0 x y : Name) {@(tactic auto) p : x ∈ α} {@(tactic auto) q : y ∈ α}
    → Dec (_≡_ {A = Σ0 Name (_∈ α)} < p > < q >)
(x ≟ y) {p} {q} = p ∈-≟ q

opaque
  unfolding _⊆_

  @0 Empty : Scope → Set
  Empty α = α ⊆ ∅

  ∅-empty : Empty ∅
  ∅-empty = < ⋈-∅-right >

  ⊆-empty : α ⊆ β → Empty β → Empty α
  ⊆-empty p e = ⊆-trans p e

opaque
  unfolding Empty

  empty-case : Empty α → @0 x ∈ α → A
  empty-case p q = ∅-case (⊆-trans q p)

opaque
  unfolding Empty _⋈_≡_

  <>-empty : Empty α → Empty β → Empty (α <> β)
  <>-empty < EmptyL > q = q
  <>-empty < EmptyR > q = q

opaque
  unfolding _⊆_

  @0 Subsingleton : @0 Name → Scope → Set
  Subsingleton x α = α ⊆ [ x ]

  []-subsingleton : Subsingleton x [ x ]
  []-subsingleton = < ⋈-∅-right >

  ⊆-subsingleton : ∀ {α β} → α ⊆ β → Subsingleton x β → Subsingleton x α
  ⊆-subsingleton p q = ⊆-trans p q

opaque
  unfolding Subsingleton

  subsingleton-case : ∀ {α} → Subsingleton x α → y ∈ α → (x ≡ y → A) → A
  subsingleton-case s p f = []-case (⊆-trans p s) (f ∘ sym)

opaque
  unfolding Subsingleton Empty _⋈_≡_

  left-subsingleton  : Subsingleton x α → Empty β → Subsingleton x (α <> β)
  left-subsingleton p < EmptyL > = subst (Subsingleton _) (sym <>-∅) p
  left-subsingleton p < EmptyR > = subst (Subsingleton _) (sym <>-∅) p

  right-subsingleton : Empty α → Subsingleton x β → Subsingleton x (α <> β)
  right-subsingleton < EmptyL > q = q
  right-subsingleton < EmptyR > q = q

opaque
  unfolding _⊆_

  @0 diff : α ⊆ β → Scope
  diff (erase p , _) = p

  diff-left : (p : α ⋈ β ≡ γ) → diff (⊆-left p) ≡ β
  diff-left p = refl

  diff-right : (p : α ⋈ β ≡ γ) → diff (⊆-right p) ≡ α
  diff-right p = refl

  ⋈-diff : (p : α ⊆ β) → α ⋈ diff p ≡ β
  ⋈-diff = proj₂

  diff-⊆ : (p : α ⊆ β) → diff p ⊆ β
  diff-⊆ p = ⊆-right (⋈-diff p)

  diff-case : (p : α ⊆ β) → x ∈ β
            → (x ∈ α → A) → (x ∈ diff p → A) → A
  diff-case p = ⋈-case (⋈-diff p)

opaque
  unfolding diff

  diff-⊆-trans : (p : α ⊆ β) (q : β ⊆ γ) → diff p ⊆ diff (⊆-trans p q)
  diff-⊆-trans < p > < q > =
    let < _ , s > = ⋈-assoc p q
    in  < s >

opaque
  unfolding coerce

  diff-coerce : (p : α ⊆ β) (q : x ∈ α) → diff q ⊆ diff (coerce p q)
  diff-coerce p q = diff-⊆-trans q p

opaque
  unfolding _⊆_

  ⊆-⋈-split : α ⊆ β → β₁ ⋈ β₂ ≡ β
    → Σ0 (Scope × Scope) λ (α₁ , α₂) → α₁ ⊆ β₁ × α₂ ⊆ β₂ × α₁ ⋈ α₂ ≡ α
  ⊆-⋈-split < p > q =
    let < r₁ , r₂ , r₃ , r₄ > = ⋈-quad p q
    in  < < r₃ > , < r₄ > , r₁ >

  ⊆-<>-split : {{Rezz β₁}} → α ⊆ (β₁ <> β₂)
    → Σ0 (Scope × Scope) λ (α₁ , α₂) → α₁ ⊆ β₁ × α₂ ⊆ β₂ × α₁ ⋈ α₂ ≡ α
  ⊆-<>-split {{r}} p = ⊆-⋈-split p (⋈-refl {{r}})



opaque
  unfolding Empty _⋈_≡_

  emptyAll : Empty α → All P α
  emptyAll < EmptyL > = All∅
  emptyAll < EmptyR > = All∅



opaque
  unfolding All _⋈_≡_

  splitAll : α ⋈ β ≡ γ → All P γ → All P α × All P β
  splitAll EmptyL ps = [] , ps
  splitAll EmptyR ps = ps , []
  splitAll (ConsL x q) (p ∷ ps) = Product.map₁ (p ∷_) (splitAll q ps)
  splitAll (ConsR x q) (p ∷ ps) = Product.map₂ (p ∷_) (splitAll q ps)


-}
