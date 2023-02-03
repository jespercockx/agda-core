
open import Utils hiding (A; B; C; P; Q; R)
open import Scope as _ using (IScope)

module ScopeImpl where

private variable
  @0 A B C : Set
  @0 P Q R : @0 A → Set

module SimpleScope (Name : Set) where

    data Scope : Set where
      ∅ : Scope
      [_] : @0 Name → Scope
      _<>_ : Scope → Scope → Scope

    data _⋈_≡_ : (@0 α β γ : Scope) → Set where
      ∅-l   : ∅  ⋈ β  ≡ β
      ∅-r   : α  ⋈ ∅  ≡ α
      join  : α  ⋈ β  ≡ (α <> β)
      swap  : α  ⋈ β  ≡ (β <> α)
      <>-ll : α₂ ⋈ β  ≡ δ → α₁ ⋈ δ  ≡ γ → (α₁ <> α₂) ⋈ β          ≡ γ
      <>-lr : α₁ ⋈ β  ≡ δ → δ  ⋈ α₂ ≡ γ → (α₁ <> α₂) ⋈ β          ≡ γ
      <>-rl : α  ⋈ β₂ ≡ δ → β₁ ⋈ δ  ≡ γ → α          ⋈ (β₁ <> β₂) ≡ γ
      <>-rr : α  ⋈ β₁ ≡ δ → δ  ⋈ β₂ ≡ γ → α          ⋈ (β₁ <> β₂) ≡ γ

    ⋈-∅-left : ∅  ⋈ β  ≡ β
    ⋈-∅-left = ∅-l

    ⋈-∅-right : α ⋈ ∅ ≡ α
    ⋈-∅-right = ∅-r
    
    ⋈-refl : α ⋈ β ≡ (α <> β)
    ⋈-refl = join

    ⋈-comm : α ⋈ β ≡ γ → β ⋈ α ≡ γ
    ⋈-comm join        = swap
    ⋈-comm swap        = join
    ⋈-comm ∅-r         = ∅-l
    ⋈-comm ∅-l         = ∅-r
    ⋈-comm (<>-ll p q) = <>-rl (⋈-comm p) q
    ⋈-comm (<>-lr p q) = <>-rr (⋈-comm p) q
    ⋈-comm (<>-rl p q) = <>-ll (⋈-comm p) q
    ⋈-comm (<>-rr p q) = <>-lr (⋈-comm p) q


    ⋈-assoc : α ⋈ β ≡ δ → δ ⋈ γ ≡ ε → α ⋈ (β <> γ) ≡ ε
    ⋈-assoc = <>-rr

    ⋈-assoc' : α ⋈ β ≡ δ → δ ⋈ γ ≡ ε → (γ <> α) ⋈ β ≡ ε
    ⋈-assoc' p q = <>-ll p (⋈-comm q)

    ⋈-<> : α₁ ⋈ α₂ ≡ α → β₁ ⋈ β₂ ≡ β → (α₁ <> β₁) ⋈ (α₂ <> β₂) ≡ (α <> β)
    ⋈-<> p q = <>-rr (<>-lr p join) (<>-ll q join)
    

{-
      -- This more general statement seems unprovable in the current representation,
      -- in particular the case `⋈-assoc join join ∅-l` requires us to prove
      -- `α ⋈ β ≡ (α <> ∅) <> β`, which cannot be proven.
      -- Is this a bug or a feature?
      ⋈-assoc : α ⋈ β ≡ δ → δ ⋈ γ ≡ ε → β ⋈ γ ≡ ζ → α ⋈ ζ ≡ ε
      ⋈-assoc ∅-l q ∅-l = q
      ⋈-assoc ∅-r q ∅-l = q
      ⋈-assoc join ∅-r ∅-l = join
      ⋈-assoc join join ∅-l = {!   !}
      ⋈-assoc join swap ∅-l = {!   !}
      ⋈-assoc join (<>-ll q₁ q₂) ∅-l = {!   !}
      ⋈-assoc join (<>-lr q₁ q₂) ∅-l = {!   !}
      ⋈-assoc join (<>-rl q₁ q₂) ∅-l = {!   !}
      ⋈-assoc join (<>-rr q₁ q₂) ∅-l = {!   !}
      ⋈-assoc swap q ∅-l = {!   !}
      ⋈-assoc (<>-ll p p₁) q ∅-l = {!   !}
      ⋈-assoc (<>-lr p p₁) q ∅-l = {!   !}
      ⋈-assoc p q ∅-r = {!   !}
      ⋈-assoc p q join = <>-rr p q
      ⋈-assoc p q swap = <>-rl p (⋈-comm q)
      ⋈-assoc {α} {β₁ <> β₂} {δ} p q (<>-ll r s) = 
        let t : (α <> β₁) ⋈ β₂ ≡ δ
            t = ⋈-comm (⋈-assoc swap (⋈-comm p) swap)
        in  ⋈-assoc join (⋈-assoc t q r) s
      ⋈-assoc p q (<>-lr r s) = {!   !}
      ⋈-assoc p q (<>-rl r s) = {!   !}
      ⋈-assoc p q (<>-rr r s) = {!   !}
-}

    _⊆_ : (α β  : Scope) → Set
    α ⊆ β = Σ0 Scope (λ γ → α ⋈ γ ≡ β)

    ⋈-left : α ⋈ β ≡ γ → α ⊆ γ
    ⋈-left p = < p >

    ⋈-right : α ⋈ β ≡ γ → β ⊆ γ
    ⋈-right p = < ⋈-comm p >

    inl : α₁ ⊆ α₂ → α₂ ⋈ β ≡ γ → α₁ ⊆ γ
    inl < p > q = < <>-rr p q >

    inr : β₁ ⊆ β₂ → α ⋈ β₂ ≡ γ → β₁ ⊆ γ
    inr < p > q = < <>-rl p q >

    ⊆-trans : α ⊆ β → β ⊆ γ → α ⊆ γ
    ⊆-trans p < q > = inl p q

    _∈_ : @0 Name → Scope → Set
    x ∈ α = [ x ] ⊆ α

    coerce : α ⊆ β → x ∈ α → x ∈ β
    coerce f p = ⊆-trans p f
    
    here : x ∈ [ x ]
    here = < ∅-r >

    left : α ⊆ β → α ⊆ (β <> γ)
    left p = inl p join

    right : α ⊆ γ → α ⊆ (β <> γ)
    right p = inr p join

    data Empty : Scope → Set where
      ∅-empty  : Empty ∅
      <>-empty  : Empty α → Empty β → Empty (α <> β)

    data _∈′_ : Name → Scope → Set where
      here′  : x ∈′ [ x ]
      left′  : x ∈′ α → x ∈′ (α <> β)
      right′ : x ∈′ β → x ∈′ (α <> β)
    
    to∈ : x ∈′ α → x ∈ α
    to∈ here′ = here
    to∈ (left′ p) = left (to∈ p)
    to∈ (right′ p) = right (to∈ p)

    coerce-left : α ⋈ β ≡ γ → x ∈′ α → x ∈′ γ
    coerce-right : α ⋈ β ≡ γ → x ∈′ β → x ∈′ γ

    coerce-left ∅-r q = q
    coerce-left join q = left′ q
    coerce-left swap q = right′ q
    coerce-left (<>-rl p₁ p₂) q = coerce-right p₂ (coerce-left p₁ q)
    coerce-left (<>-rr p₁ p₂) q = coerce-left p₂ (coerce-left p₁ q)
    coerce-left (<>-ll p₁ p₂) (left′ q) = coerce-left p₂ q
    coerce-left (<>-ll p₁ p₂) (right′ q) = coerce-right p₂ (coerce-left p₁ q)
    coerce-left (<>-lr p₁ p₂) (left′ q) = coerce-left p₂ (coerce-left p₁ q)
    coerce-left (<>-lr p₁ p₂) (right′ q) = coerce-right p₂ q

    coerce-right ∅-l q = q
    coerce-right join q = right′ q
    coerce-right swap q = left′ q
    coerce-right (<>-ll p₁ p₂) q = coerce-right p₂ (coerce-right p₁ q)
    coerce-right (<>-lr p₁ p₂) q = coerce-left p₂ (coerce-right p₁ q)
    coerce-right (<>-rl p₁ p₂) (left′ q) = coerce-left p₂ q
    coerce-right (<>-rl p₁ p₂) (right′ q) = coerce-right p₂ (coerce-right p₁ q)
    coerce-right (<>-rr p₁ p₂) (left′ q) = coerce-left p₂ (coerce-right p₁ q)
    coerce-right (<>-rr p₁ p₂) (right′ q) = coerce-right p₂ q

    from∈ : x ∈ α → x ∈′ α
    from∈ < p > = coerce-left p here′

    fromto∈ : (p : x ∈′ α) → from∈ (to∈ p) ≡ p
    fromto∈ here′ = refl
    fromto∈ (left′ p)  rewrite fromto∈ p = refl
    fromto∈ (right′ p) rewrite fromto∈ p = refl

    -- Since `∅ <> ∅` is not equal to `∅`, our proofs of elementhood are not canonical.
    -- N.B. This does not necessarily mean that our *separations* are non-canonical.
    -- (this is still an open question)
    --private abstract
    --  tofrom∈ : (p : x ∈ α) → to∈ (from∈ p) ≡ p
    --  tofrom∈ = {!   !}

    ∅-case′ : @0 x ∈′ ∅ → A
    ∅-case′ ()

    ∅-case : @0 x ∈ ∅ → A
    ∅-case p = ∅-case′ (from∈ p)

    []-case′ : @0 x ∈′ [ y ] → (x ≡ y → A) → A
    []-case′ here′ f = f refl

    []-case : @0 x ∈ [ y ] → (x ≡ y → A) → A
    []-case p = []-case′ (from∈ p)

    <>-case : x ∈ (α <> β) → (x ∈ α → A) → (x ∈ β → A) → A
    <>-case p f g = case (from∈ p) of λ where 
      (left′ pl)  → f (to∈ pl)
      (right′ pr) → g (to∈ pr)

    ⋈-case : α ⋈ β ≡ γ → x ∈ γ → (x ∈ α → A) → (x ∈ β → A) → A
    ⋈-case ∅-l q f g = g q
    ⋈-case ∅-r q f g = f q
    ⋈-case join q f g = <>-case q f g
    ⋈-case swap q f g = <>-case q g f
    ⋈-case (<>-ll p₁ p₂) q f g = ⋈-case p₂ q (f ∘ left) λ r → ⋈-case p₁ r (f ∘ right) g
    ⋈-case (<>-lr p₁ p₂) q f g = ⋈-case p₂ q (λ r → ⋈-case p₁ r (f ∘ left) g) (f ∘ right)
    ⋈-case (<>-rl p₁ p₂) q f g = ⋈-case p₂ q (g ∘ left) (λ r → ⋈-case p₁ r f (g ∘ right))
    ⋈-case (<>-rr p₁ p₂) q f g = ⋈-case p₂ q (λ r → ⋈-case p₁ r f (g ∘ left)) (g ∘ right)

    -- TODO: convince Agda that this is terminating
    {-# NON_TERMINATING #-}
    ⋈-quad : α₁ ⋈ α₂ ≡ γ → β₁ ⋈ β₂ ≡ γ
             → Σ0 (Scope × Scope × Scope × Scope) λ (γ₁ , γ₂ , γ₃ , γ₄) →
               (γ₁ ⋈ γ₂ ≡ α₁) × (γ₃ ⋈ γ₄ ≡ α₂) × (γ₁ ⋈ γ₃ ≡ β₁) × (γ₂ ⋈ γ₄ ≡ β₂)
    ⋈-quad ∅-l q = < ∅-l , q , ∅-l , ∅-l >
    ⋈-quad ∅-r q = < q , ∅-r , ∅-r , ∅-r >
    ⋈-quad p ∅-l = < ∅-l , ∅-l , ∅-l , p >
    ⋈-quad p ∅-r = < ∅-r , ∅-r , p , ∅-r >
    ⋈-quad join join = < ∅-r , ∅-l , ∅-r , ∅-l >
    ⋈-quad join swap = < ∅-l , ∅-r , ∅-l , ∅-r >
    ⋈-quad swap join = < ∅-l , ∅-r , ∅-l , ∅-r >
    ⋈-quad swap swap = < ∅-r , ∅-l , ∅-r , ∅-l >
    ⋈-quad {α₃ <> α₄} {α₂} {γ} {β₁} {β₂} (<>-ll {α₂ = α₄} {δ = δ} {α₁ = α₃} p₁ p₂) q = 
      let (erase (γ₁ , γ₂ , γ₃ , γ₄) , (q₁ , q₂ , q₃ , q₄)) = ⋈-quad {α₃} {δ} {γ} {β₁} {β₂} p₂ q
          (erase (δ₁ , δ₂ , δ₃ , δ₄) , (r₁ , r₂ , r₃ , r₄)) = ⋈-quad {α₄} {α₂} {δ} {γ₃} {γ₄} p₁ q₂
      in  (erase ((γ₁ <> δ₁) , (γ₂ <> δ₂) , δ₃ , δ₄) , (⋈-<> q₁ r₁ , r₂ , <>-ll r₃ q₃ , <>-ll r₄ q₄))
    ⋈-quad {α₃ <> α₄} {α₂} {γ} {β₁} {β₂} (<>-lr {α₁ = α₃} {δ = δ} {α₂ = α₄} p₁ p₂) q = 
      let (erase (γ₁ , γ₂ , γ₃ , γ₄) , (q₁ , q₂ , q₃ , q₄)) = ⋈-quad p₂ q
          (erase (δ₁ , δ₂ , δ₃ , δ₄) , (r₁ , r₂ , r₃ , r₄)) = ⋈-quad {α₃} {α₂} {δ} {γ₁} {γ₂} p₁ q₁
      in  < ⋈-<> r₁ q₂ , r₂ , <>-lr r₃ q₃ , <>-lr r₄ q₄ >
    ⋈-quad {α₁} {β₃ <> β₄} {γ} {β₁} {β₂} (<>-rl {β₂ = β₄} {δ = δ} {β₁ = β₃} p₁ p₂) q = 
      let (erase (γ₁ , γ₂ , γ₃ , γ₄) , (q₁ , q₂ , q₃ , q₄)) = ⋈-quad p₂ q
          (erase (δ₁ , δ₂ , δ₃ , δ₄) , (r₁ , r₂ , r₃ , r₄)) = ⋈-quad {α₁} {β₄} {δ} {γ₃} {γ₄} p₁ q₂
      in  < r₁ , ⋈-<> q₁ r₂ , <>-rl r₃ q₃ , <>-rl r₄ q₄ >
    ⋈-quad {α₁} {β₃ <> β₄} {γ} {β₁} {β₂} (<>-rr {β₁ = β₃} {δ = δ} {β₂ = β₄} p₁ p₂) q = 
      let (erase (γ₁ , γ₂ , γ₃ , γ₄) , (q₁ , q₂ , q₃ , q₄)) = ⋈-quad p₂ q
          (erase (δ₁ , δ₂ , δ₃ , δ₄) , (r₁ , r₂ , r₃ , r₄)) = ⋈-quad {α₁} {β₃} {δ} {γ₁} {γ₂} p₁ q₁
      in  < r₁ , ⋈-<> r₂ q₂ , <>-rr r₃ q₃ , <>-rr r₄ q₄ >
    ⋈-quad {α₁} {α₂} {γ} {α₃ <> α₄} {β₂} p (<>-ll {α₂ = α₄} {δ = δ} {α₁ = α₃} q₁ q₂) = 
      let (erase (γ₁ , γ₂ , γ₃ , γ₄) , (p₁ , p₂ , p₃ , p₄)) = ⋈-quad p q₂
          (erase (δ₁ , δ₂ , δ₃ , δ₄) , (r₁ , r₂ , r₃ , r₄)) = ⋈-quad {γ₂} {γ₄} {δ} {α₄} {β₂} p₄ q₁
      in  < <>-ll r₁ p₁ , <>-ll r₂ p₂ , ⋈-<> p₃ r₃ , r₄ >
    ⋈-quad {α₁} {α₂} {γ} {α₃ <> α₄} {β₂} p (<>-lr {α₁ = α₃} {δ = δ} {α₂ = α₄} q₁ q₂) = 
      let (erase (γ₁ , γ₂ , γ₃ , γ₄) , (p₁ , p₂ , p₃ , p₄)) = ⋈-quad p q₂
          (erase (δ₁ , δ₂ , δ₃ , δ₄) , (r₁ , r₂ , r₃ , r₄)) = ⋈-quad {γ₁} {γ₃} {δ} {α₃} {β₂} p₃ q₁
      in  < <>-lr r₁ p₁ , <>-lr r₂ p₂ , ⋈-<> r₃ p₄ , r₄ >
    ⋈-quad {α₁} {α₂} {γ} {β₁} {β₃ <> β₄} p (<>-rl {β₂ = β₄} {δ = δ} {β₁ = β₃} q₁ q₂) = 
      let (erase (γ₁ , γ₂ , γ₃ , γ₄) , (p₁ , p₂ , p₃ , p₄)) = ⋈-quad p q₂
          (erase (δ₁ , δ₂ , δ₃ , δ₄) , (r₁ , r₂ , r₃ , r₄)) = ⋈-quad {γ₂} {γ₄} {δ} {β₁} {β₄} p₄ q₁
      in  < <>-rl r₁ p₁ , <>-rl r₂ p₂ , r₃ , ⋈-<> p₃ r₄ >
    ⋈-quad {α₁} {α₂} {γ} {β₁} {β₃ <> β₄} p (<>-rr {β₁ = β₃} {δ = δ} {β₂ = β₄} q₁ q₂) = 
      let (erase (γ₁ , γ₂ , γ₃ , γ₄) , (p₁ , p₂ , p₃ , p₄)) = ⋈-quad p q₂
          (erase (δ₁ , δ₂ , δ₃ , δ₄) , (r₁ , r₂ , r₃ , r₄)) = ⋈-quad {γ₁} {γ₃} {δ} {β₁} {β₃} p₃ q₁
      in  < <>-rr r₁ p₁ , <>-rr r₂ p₂ , r₃ , ⋈-<> r₄ p₄  >

    module BNT where
      data BNT : Set where
        tip : ℕ → BNT
        bin : ℕ → BNT → BNT → BNT
  
      bin-injective-left : bin x₁ y₁ z₁ ≡ bin x₂ y₂ z₂ → y₁ ≡ y₂
      bin-injective-left refl = refl

      bin-injective-right : bin x₁ y₁ z₁ ≡ bin x₂ y₂ z₂ → z₁ ≡ z₂
      bin-injective-right refl = refl
  
      _≟_ : (x y : BNT) → Dec (x ≡ y)
      tip k       ≟ tip l  = case (k Nat.≟ l) of λ where
        (yes eq) → yes (cong tip eq)
        (no f)   → no λ { refl → f refl }
      tip k       ≟ bin l y₁ y₂ = no λ ()
      bin k x₁ x₂ ≟ tip l       = no λ ()
      bin k x₁ x₂ ≟ bin l y₁ y₂ = 
        case k Nat.≟ l of λ where
          (no f)     → no λ { refl → f refl }
          (yes refl) → case (x₁ ≟ y₁) of λ where
            (no f)     → no λ { refl → f refl }
            (yes refl) → case (x₂ ≟ y₂) of λ where
              (no f)     → no λ { refl → f refl }
              (yes refl) → yes refl

    open BNT hiding (_≟_)

    ⋈toBNT : α ⋈ β ≡ γ → BNT
    ⋈toBNT ∅-l = tip 0
    ⋈toBNT ∅-r = tip 1
    ⋈toBNT join = tip 2
    ⋈toBNT swap = tip 3
    ⋈toBNT (<>-ll p q) = bin 0 (⋈toBNT p) (⋈toBNT q)
    ⋈toBNT (<>-lr p q) = bin 1 (⋈toBNT p) (⋈toBNT q)
    ⋈toBNT (<>-rl p q) = bin 2 (⋈toBNT p) (⋈toBNT q)
    ⋈toBNT (<>-rr p q) = bin 3 (⋈toBNT p) (⋈toBNT q)

    ⋈toBNT-injective' : (p : α ⋈ β ≡ γ₁) (q : α ⋈ β ≡ γ₂) 
                    → ⋈toBNT p ≡ ⋈toBNT q 
                    → Σ (γ₁ ≡ γ₂) λ γ= → PathOver (α ⋈ β ≡_) γ= p q
    ⋈toBNT-injective' ∅-l  ∅-l  eq = refl , refl
    ⋈toBNT-injective' ∅-r  ∅-r  eq = refl , refl
    ⋈toBNT-injective' join join eq = refl , refl
    ⋈toBNT-injective' swap swap eq = refl , refl
    ⋈toBNT-injective' (<>-ll p₁ p₂) (<>-ll q₁ q₂) eq 
                    with ⋈toBNT-injective' p₁ q₁ (bin-injective-left eq)
    ... | refl , refl with ⋈toBNT-injective' p₂ q₂ (bin-injective-right eq)
    ... | refl , refl = refl , refl
    ⋈toBNT-injective' (<>-lr p₁ p₂) (<>-lr q₁ q₂) eq
                    with ⋈toBNT-injective' p₁ q₁ (bin-injective-left eq)
    ... | refl , refl with ⋈toBNT-injective' p₂ q₂ (bin-injective-right eq)
    ... | refl , refl = refl , refl
    ⋈toBNT-injective' (<>-rl p₁ p₂) (<>-rl q₁ q₂) eq 
                    with ⋈toBNT-injective' p₁ q₁ (bin-injective-left eq)
    ... | refl , refl with ⋈toBNT-injective' p₂ q₂ (bin-injective-right eq)
    ... | refl , refl = refl , refl
    ⋈toBNT-injective' (<>-rr p₁ p₂) (<>-rr q₁ q₂) eq
                    with ⋈toBNT-injective' p₁ q₁ (bin-injective-left eq)
    ... | refl , refl with ⋈toBNT-injective' p₂ q₂ (bin-injective-right eq)
    ... | refl , refl = refl , refl

    ⋈toBNT-injective : (p q : α ⋈ β ≡ γ) → ⋈toBNT p ≡ ⋈toBNT q → p ≡ q
    ⋈toBNT-injective p q eq = case ⋈toBNT-injective' p q eq of λ where
      (refl , eq) → eq

    _⋈-≟_ : (p q : α ⋈ β ≡ γ) → Dec (p ≡ q)
    p ⋈-≟ q = case ⋈toBNT p BNT.≟ ⋈toBNT q of λ where
      (yes eq) → yes (⋈toBNT-injective p q eq)
      (no f)   → no (f ∘ cong ⋈toBNT)

    ⊆toBNT : α ⊆ β → BNT
    ⊆toBNT < p > = ⋈toBNT p

    ⋈toBNT-injective'' 
      : (p : α₁ ⋈ β₁ ≡ γ) (q : α₂ ⋈ β₂ ≡ γ) 
      → ⋈toBNT p ≡ ⋈toBNT q 
      → Σ ((α₁ ≡ α₂) × (β₁ ≡ β₂)) λ (α= , β=) → 
          let αβ= = cong₂ _,_ α= β=
          in  PathOver (λ (α , β) → α ⋈ β ≡ γ) αβ= p q
    ⋈toBNT-injective'' ∅-l ∅-l eq = (refl , refl) , refl
    ⋈toBNT-injective'' ∅-r ∅-r eq = (refl , refl) , refl
    ⋈toBNT-injective'' join join eq = (refl , refl) , refl
    ⋈toBNT-injective'' swap swap eq = (refl , refl) , refl
    ⋈toBNT-injective'' (<>-ll p₁ p₂) (<>-ll q₁ q₂) eq 
                                with ⋈toBNT-injective'' p₂ q₂ (bin-injective-right eq)
    ... | (refl , refl) , refl with ⋈toBNT-injective'' p₁ q₁ (bin-injective-left eq)
    ... | (refl , refl) , refl = (refl , refl) , refl
    ⋈toBNT-injective'' (<>-lr p₁ p₂) (<>-lr q₁ q₂) eq
                                with ⋈toBNT-injective'' p₂ q₂ (bin-injective-right eq)
    ... | (refl , refl) , refl with ⋈toBNT-injective'' p₁ q₁ (bin-injective-left eq)
    ... | (refl , refl) , refl = (refl , refl) , refl
    ⋈toBNT-injective'' (<>-rl p₁ p₂) (<>-rl q₁ q₂) eq
                                with ⋈toBNT-injective'' p₂ q₂ (bin-injective-right eq)
    ... | (refl , refl) , refl with ⋈toBNT-injective'' p₁ q₁ (bin-injective-left eq)
    ... | (refl , refl) , refl = (refl , refl) , refl
    ⋈toBNT-injective'' (<>-rr p₁ p₂) (<>-rr q₁ q₂) eq
                                with ⋈toBNT-injective'' p₂ q₂ (bin-injective-right eq)
    ... | (refl , refl) , refl with ⋈toBNT-injective'' p₁ q₁ (bin-injective-left eq)
    ... | (refl , refl) , refl = (refl , refl) , refl

    ⊆toBNT-injective : (p q : α ⊆ β) → ⊆toBNT p ≡ ⊆toBNT q → p ≡ q
    ⊆toBNT-injective < p > < q > eq = case ⋈toBNT-injective'' p q eq of λ where
      ((refl , refl) , refl) → refl

    _⊆-≟_ : (p q : α ⊆ β) → Dec (p ≡ q)
    p ⊆-≟ q = case ⊆toBNT p BNT.≟ ⊆toBNT q of λ where
      (yes eq) → yes (⊆toBNT-injective p q eq)
      (no f)   → no  (f ∘ cong ⊆toBNT)

    ∈toBNT : x ∈ α → BNT
    ∈toBNT = ⊆toBNT

    ∈toBNT-injective : (p : x ∈ α) (q : y ∈ α) 
                    → ∈toBNT p ≡ ∈toBNT q 
                    → _≡_ {A = Σ Name (_∈ α)} (x , p) (y , q)
    ∈toBNT-injective < p > < q > eq with ⋈toBNT-injective'' p q eq
    ... | (refl , refl) , refl = refl

    _∈-≟_ : (p : x ∈ α) (q : y ∈ α) → Dec (_≡_ {A = Σ Name (_∈ α)} (x , p) (y , q))
    _∈-≟_ {x = x} p q with ⊆toBNT p BNT.≟ ⊆toBNT q
    ... | yes eq = yes (∈toBNT-injective p q eq)
    ... | no f   = no (λ { refl → f refl })

    rezz-<> : Rezz x → Rezz y → Rezz (x <> y)
    rezz-<> = rezz-cong₂ _<>_

    rezz-⋈ : α ⋈ β ≡ γ → Rezz γ → Rezz α × Rezz β
    rezz-⋈ ∅-l r = rezz ∅ , r
    rezz-⋈ ∅-r r = r , rezz ∅
    rezz-⋈ join (rezz (α <> β)) = rezz α , rezz β
    rezz-⋈ swap (rezz (β <> α)) = rezz α , rezz β
    rezz-⋈ (<>-ll p q) r = 
      let (rq₁ , rq₂) = rezz-⋈ q r
          (rp₁ , rp₂) = rezz-⋈ p rq₂
      in  rezz-<> rq₁ rp₁ , rp₂
    rezz-⋈ (<>-lr p q) r = 
      let (rq₁ , rq₂) = rezz-⋈ q r
          (rp₁ , rp₂) = rezz-⋈ p rq₁
      in  rezz-<> rp₁ rq₂ , rp₂
    rezz-⋈ (<>-rl p q) r = 
      let (rq₁ , rq₂) = rezz-⋈ q r
          (rp₁ , rp₂) = rezz-⋈ p rq₂
      in  rp₁ , rezz-<> rq₁ rp₂
    rezz-⋈ (<>-rr p q) r = 
      let (rq₁ , rq₂) = rezz-⋈ q r
          (rp₁ , rp₂) = rezz-⋈ p rq₁
      in  rp₁ , rezz-<> rp₂ rq₂


simpleScope : (Name : Set) → IScope Name
simpleScope Name = record { SimpleScope Name }
