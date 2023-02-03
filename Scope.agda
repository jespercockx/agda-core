-- An abstract interface to representations of scopes


{- Design constraints:
- Well-scoped syntax
- Abstract interface for working with scopes
- Possibility to construct from a proof of x ∈ α a "remainder scope" α' with x removed
- Joining two scopes α and β should only increase the size of the indices by a constant
- Scopes are runtime-irrelevant
-}

open import Utils hiding (A; B; C; P; Q; R)

module Scope (Name : Set) where

private variable
  @0 A B C : Set
  @0 P Q R : @0 A → Set

record IScope : Set₁ where
  no-eta-equality
  field
    Scope : Set
    ∅     : Scope
    [_]   : @0 Name → Scope
    _<>_  : Scope → Scope → Scope

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
    -- This is formulated in continuation-passing style to make them more efficient and easier to use.
    ∅-case  : @0 (x ∈ ∅) → A
    []-case : @0 (x ∈ [ y ]) → (x ≡ y → A) → A
    ⋈-case : α ⋈ β ≡ γ → x ∈ γ → (x ∈ α → A) → (x ∈ β → A) → A

  field
    ⋈-quad : α₁ ⋈ α₂ ≡ γ → β₁ ⋈ β₂ ≡ γ
            → Σ0 (Scope × Scope × Scope × Scope) λ (γ₁ , γ₂ , γ₃ , γ₄) →
              (γ₁ ⋈ γ₂ ≡ α₁) × (γ₃ ⋈ γ₄ ≡ α₂) × (γ₁ ⋈ γ₃ ≡ β₁) × (γ₂ ⋈ γ₄ ≡ β₂)

  field
    _⋈-≟_ : (p q : α ⋈ β ≡ γ) → Dec (p ≡ q)
    _⊆-≟_ : (p q : α ⊆ β) → Dec (p ≡ q)
    _∈-≟_ : (p : x ∈ α) (q : y ∈ α) → Dec (_≡_ {A = Σ Name (_∈ α)} (x , p) (y , q))

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

  Empty : Scope → Set
  Empty α = α ⊆ ∅

  ∅-empty : Empty ∅
  ∅-empty = < ⋈-∅-right >

  <>-empty : Empty α → Empty β → Empty (α <> β)
  <>-empty < p > < q > = < ⋈-assoc (⋈-assoc' q ⋈-∅-left) p >

  ⊆-empty : α ⊆ β → Empty β → Empty α
  ⊆-empty p e = ⊆-trans p e

  empty-case : Empty α → @0 x ∈ α → A
  empty-case p q = ∅-case (⊆-trans q p)

  Subsingleton : @0 Name → Scope → Set
  Subsingleton x α = α ⊆ [ x ]

  []-subsingleton : Subsingleton x [ x ]
  []-subsingleton = < ⋈-∅-right >

  left-subsingleton  : Subsingleton x α → Empty β → Subsingleton x (α <> β)
  left-subsingleton < p > < q > = < ⋈-assoc (⋈-assoc' q ⋈-∅-left) p >

  right-subsingleton : Empty α → Subsingleton x β → Subsingleton x (α <> β)
  right-subsingleton < p > < q > = < ⋈-assoc (⋈-comm (⋈-assoc (⋈-comm p) ⋈-∅-left)) q >

  ⊆-subsingleton : α ⊆ β → Subsingleton x β → Subsingleton x α
  ⊆-subsingleton p q = ⊆-trans p q

  subsingleton-case : Subsingleton x α → @0 y ∈ α → (x ≡ y → A) → A
  subsingleton-case s p f = []-case (⊆-trans p s) (f ∘ sym)

  <>-case  : x ∈ (α <> β) → (x ∈ α → A) → (x ∈ β → A) → A
  <>-case = ⋈-case ⋈-refl

  ◃-case : x ∈ (y ◃ α) → (x ≡ y → A) → (x ∈ α → A) → A
  ◃-case p f g = <>-case p (λ q → []-case q f) g


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

  ⊆-⋈-split : α ⊆ β → β₁ ⋈ β₂ ≡ β 
          → Σ0 (Scope × Scope) λ (α₁ , α₂) → α₁ ⊆ β₁ × α₂ ⊆ β₂ × α₁ ⋈ α₂ ≡ α
  ⊆-⋈-split < p > q = 
    let < r₁ , r₂ , r₃ , r₄ > = ⋈-quad p q
    in  < < r₃ > , < r₄ > , r₁ >

  ⊆-<>-split : α ⊆ (β₁ <> β₂) → Σ0 (Scope × Scope) λ (α₁ , α₂) → α₁ ⊆ β₁ × α₂ ⊆ β₂ × α₁ ⋈ α₂ ≡ α
  ⊆-<>-split p = ⊆-⋈-split p ⋈-refl

  -- `All P α` is a first-order representation of the type `(x ∈ α) → P x`
  data All (P : @0 Name → Set) : @0 Scope → Set where
    constAll : (∀ {@0 x} {{@0 _ : x ∈ α}} → P x) → All P α
    ⋈All : α ⋈ β ≡ γ → All P α → All P β → All P γ
  
  emptyAll : Empty α → All P α
  emptyAll e = constAll λ {{i}} → empty-case e i

  subsingleAll : Subsingleton x α → P x → All P α
  subsingleAll s p = constAll λ {{i}} → subsingleton-case s i (λ eq → subst _ eq p)

  ∅All : All P ∅
  ∅All = emptyAll ∅-empty

  []All : P x → All P [ x ]
  []All = subsingleAll []-subsingleton

  <>All : All P α → All P β → All P (α <> β)
  <>All = ⋈All ⋈-refl

  lookupAll : All P α → x ∈ α → P x
  lookupAll (constAll p) s = p {{s}}
  lookupAll (⋈All r ps qs) s = ⋈-case r s (lookupAll ps) (lookupAll qs)
  
  _!_ : All P α → (@0 x : Name) → {{x ∈ α}} → P x
  (ps ! _) {{s}} = lookupAll ps s
  
  mapAll : (f : ∀ {@0 x} → P x → Q x) → All P α → All Q α
  mapAll f (constAll p) = constAll (f p)
  mapAll f (⋈All r ps qs) = ⋈All r (mapAll f ps) (mapAll f qs)

  --tabulateAll : {α : Scope} → (f : (@0 x : Name) → {{x ∈ α}} → P x) → All P α
  --tabulateAll {P = P} {α = α} f = ?
  {-= ⋈-elim (λ α → (f : (@0 x : Name) → {{x ∈ α}} → P x) → All P α) 
                      (λ f → ∅All) 
                      (λ f → []All (f _ {{⊆-refl}})) 
                      (λ s ps qs f → ⋈All s (ps (λ x {{i}} → f x {{coerce < s > i}})) 
                                             (qs (λ x {{i}} → f x {{coerce < ⋈-comm s > i }}))) -}

  rezz-⊆ : α ⊆ β → Rezz β → Rezz α
  rezz-⊆ < p > r = proj₁ (rezz-⋈ p r)

  rezz-Empty : Empty α → Rezz α
  rezz-Empty e = rezz-⊆ e (rezz ∅)

  rezz-Subsingleton : Subsingleton x α → Rezz α
  rezz-Subsingleton s = rezz-⊆ s (rezz [ _ ])


{- Can we implement this? Or do we need to add something to the interface?
  splitAll : α ⋈ β ≡ γ → All P γ → All P α × All P β
  splitAll s ∅All = {!  !}
  splitAll s ([]All x) = {!   !}
  splitAll s (⋈All r ps qs) = {!   !}
-}
