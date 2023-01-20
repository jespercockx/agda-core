-- An abstract interface to representations of scopes


{- Design constraints:
- Well-scoped syntax
- Abstract interface for working with scopes
- Possibility to construct from a proof of x ∈ α a "remainder scope" α' with x removed
- Joining two scopes α and β should only increase the size of the indices by a constant
- Scopes are runtime-irrelevant
-}

open import Utils hiding (A; B; C; P; Q; R)

module Scope where

private variable
  @0 A B C : Set
  @0 P Q R : @0 A → Set

record IScope (Name : Set) : Set₁ where
  no-eta-equality
  field
    Scope : Set
    ∅     : Scope
    [_]   : @0 Name → Scope
    _<>_  : Scope → Scope → Scope

  field
    Empty    : Scope → Set
    ∅-empty  : Empty ∅
    <>-empty : Empty α → Empty β → Empty (α <> β)

  field
    Singleton       : @0 Name → Scope → Set
    []-singleton    : Singleton x [ x ]
    left-singleton  : Singleton x α → Empty β → Singleton x (α <> β)
    right-singleton : Empty α → Singleton x β → Singleton x (α <> β)

  field
    _⋈_≡_         : (@0 α β γ : Scope) → Set
    ⋈-∅-left      : ∅ ⋈ β ≡ β
    ⋈-∅-right     : α ⋈ ∅ ≡ α
    ⋈-refl        : α ⋈ β ≡ (α <> β)
    ⋈-comm        : α ⋈ β ≡ γ → β ⋈ α ≡ γ
    ⋈-assoc       : α ⋈ β ≡ δ → δ ⋈ γ ≡ ε → α ⋈ (β <> γ) ≡ ε
    ⋈-assoc'      : α ⋈ β ≡ δ → δ ⋈ γ ≡ ε → (γ <> α) ⋈ β ≡ ε

  _⊆_ : (α β  : Scope) → Set
  α ⊆ β = Σ0 Scope (λ γ → α ⋈ γ ≡ β)

  _∈_  : @0 Name → Scope → Set
  x ∈ α = [ x ] ⊆ α

  field
    _⋈-≟_ : (p q : α ⋈ β ≡ γ) → Dec (p ≡ q)
    _⊆-≟_ : (p q : α ⊆ β) → Dec (p ≡ q)
    _∈-≟_ : (p : x ∈ α) (q : y ∈ α) → Dec (_≡_ {A = Σ Name (_∈ α)} (x , p) (y , q))

  -- We should have the following equivalences:
  -- 1. x ∈ ∅        ≃  ⊥
  -- 2. x ∈ [ y ]    ≃  x ≡ y
  -- 3. x ∈ (α ⋈ β)  ≃  x ∈ α ⊎ x ∈ β
  -- Unfortunaltely, demanding equivalences is perhaps too strong (see implementation below)
  -- However, we could prove that these are retractions, if needed

  -- These are formulated in continuation-passing style to make them more efficient and easier to use.
  field
    empty-case : Empty α → x ∈ α → A
    singleton-case : Singleton x α → y ∈ α → (x ≡ y → A) → A
    ⋈-case : α ⋈ β ≡ γ → x ∈ γ → (x ∈ α → A) → (x ∈ β → A) → A

  field
    All : (P : @0 Name → Set) → Scope → Set
    singleton-All : Singleton x α → All P α → P x
    ⋈-All : α ⋈ β ≡ γ → All P γ → All P α × All P β
    -- Note: mapping and tabulation require a run-time representation of the scope!
    mapAll : (α : Scope) (f : ∀ {@0 x} → P x → Q x) → All P α → All Q α
    tabulateAll : {α : Scope} → (f : (@0 x : Name) → {{x ∈ α}} → P x) → All P α

  field
    rezz-⋈ : α ⋈ β ≡ γ → Rezz γ → Rezz α × Rezz β

  _≟_ : (@0 x y : Name) {{p : x ∈ α}} {{q : y ∈ α}} 
      → Dec (_≡_ {A = Σ Name (_∈ α)} (x , p) (y , q))
  x ≟ y = it ∈-≟ it

  _◃_   : @0 Name → Scope → Scope
  x ◃ α = [ x ] <> α

  infixr 10 _◃_

  ⊆-trans : α ⊆ β → β ⊆ γ → α ⊆ γ
  ⊆-trans < p > < q > = < ⋈-assoc p q >

  coerce : α ⊆ β → x ∈ α → x ∈ β
  coerce p q = ⊆-trans q p

  ⊆-left : α ⋈ β ≡ γ → α ⊆ γ
  ⊆-left p = < p >

  ⊆-right : α ⋈ β ≡ γ → β ⊆ γ
  ⊆-right p = < ⋈-comm p >

  ⊆-∅ : ∅ ⊆ α
  ⊆-∅ = ⊆-left ⋈-∅-left

  ⊆-refl : α ⊆ α
  ⊆-refl = ⊆-left ⋈-∅-right

  left : α ⊆ β → α ⊆ (β <> γ)
  left p = ⊆-trans p (⊆-left ⋈-refl)

  right : α ⊆ γ → α ⊆ (β <> γ)
  right p = ⊆-trans p (⊆-right ⋈-refl)

  here : x ∈ (x ◃ α)
  here = ⊆-left ⋈-refl

  there : x ∈ α → x ∈ (y ◃ α)
  there p = right p

  ⊆-<> : β₁ ⊆ β₂ → (α <> β₁) ⊆ (α <> β₂)
  ⊆-<> p = < ⋈-assoc' (proj₂ p) (⋈-comm ⋈-refl) >
      
  ⊆-◃  : α ⊆ β → (y ◃ α) ⊆ (y ◃ β)
  ⊆-◃ = ⊆-<>

  ∅-case : (x ∈ ∅) → A
  ∅-case = empty-case ∅-empty

  []-case  : (x ∈ [ y ]) → (x ≡ y → A) → A
  []-case p f = singleton-case []-singleton p (f ∘ sym)

  <>-case  : x ∈ (α <> β) → (x ∈ α → A) → (x ∈ β → A) → A
  <>-case = ⋈-case ⋈-refl

  ◃-case : x ∈ (y ◃ α) → (x ≡ y → A) → (x ∈ α → A) → A
  ◃-case p f g = <>-case p (λ q → []-case q f) g

  _!_ : All P α → (@0 x : Name) → {{x ∈ α}} → P x
  (ps ! x) {{< q >}} = singleton-All []-singleton (proj₁ (⋈-All q ps))

  @0 diff : α ⊆ β → Scope
  diff = get ∘ proj₁

  diff-left : (p : α ⋈ β ≡ γ) → diff (⊆-left p) ≡ β
  diff-left p = refl

  diff-right : (p : α ⋈ β ≡ γ) → diff (⊆-right p) ≡ α
  diff-right p = refl

  ⋈-diff : (p : α ⊆ β) → α ⋈ diff p ≡ β
  ⋈-diff = proj₂

  diff-⊆-trans : (p : α ⊆ β) (q : β ⊆ γ) → diff p ⊆ diff (⊆-trans p q)
  diff-⊆-trans p q = < ⋈-refl >

  diff-⊆ : (p : α ⊆ β) → diff p ⊆ β
  diff-⊆ p = ⊆-right (⋈-diff p)

  diff-case : (p : α ⊆ β) → x ∈ β → (x ∈ α → A) → (x ∈ diff p → A) → A
  diff-case p = ⋈-case (⋈-diff p)

  rezz-⊆ : α ⊆ β → Rezz β → Rezz α
  rezz-⊆ < p > r = proj₁ (rezz-⋈ p r)

{-
open IScope {{...}} public

{-# DISPLAY IScope.Scope   iScope     = Scope       #-}
{-# DISPLAY IScope._∈_     iScope x y = x ∈ y       #-}
{-# DISPLAY IScope.∅       iScope     = ∅           #-}
{-# DISPLAY IScope.[_]     iScope x   = [ x ]       #-}
{-# DISPLAY IScope._◃_     iScope x y = x ◃ y       #-}
{-# DISPLAY IScope._⋈_     iScope x y = x ⋈ y      #-}
{-# DISPLAY IScope._⊆_     iScope x y = x ⊆ y       #-}
{-# DISPLAY IScope.coerce  iScope f p = coerce f p  #-}
{-# DISPLAY IScope.⊆-refl  iScope     = ⊆-refl      #-}
{-# DISPLAY IScope.⊆-trans iScope f g = ⊆-trans f g #-}
{-# DISPLAY IScope.⊆-∅     iScope     = ⊆-∅         #-}
{-# DISPLAY IScope.⊆-◃     iScope f   = ⊆-◃ f       #-}
{-# DISPLAY IScope.⊆-⋈     iScope f g = ⊆-⋈ f g    #-}
{-# DISPLAY IScope.here    iScope     = here        #-}
{-# DISPLAY IScope.left    iScope p   = left p      #-}
{-# DISPLAY IScope.right   iScope p   = right p     #-}
{-# DISPLAY IScope.nowhere iScope p   = nowhere p   #-}
{-# DISPLAY IScope.[]-case iScope p   = []-case p   #-}
{-# DISPLAY IScope.⋈-case  iScope p   = ⋈-case p   #-}
-}