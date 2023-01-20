
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

    is-empty′ : Empty α → x ∈′ α → A
    is-empty′ (<>-empty e₁ e₂) (left′ p) = is-empty′ e₁ p
    is-empty′ (<>-empty e₁ e₂) (right′ p) = is-empty′ e₂ p

    empty-case : Empty α → x ∈ α → A
    empty-case e p = is-empty′ e (from∈ p)

    []-case′ : x ∈′ [ y ] → (x ≡ y → A) → A
    []-case′ here′ f = f refl

    []-case : x ∈ [ y ] → (x ≡ y → A) → A
    []-case p = []-case′ (from∈ p)

    data Singleton : @0 Name → Scope → Set where
      []-singleton : Singleton x [ x ] 
      left-singleton : Singleton x α → Empty β → Singleton x (α <> β)
      right-singleton : Empty α → Singleton x β → Singleton x (α <> β)

    singleton-case′ : Singleton x α → y ∈′ α → (x ≡ y → A) → A
    singleton-case′ []-singleton here′ f = f refl
    singleton-case′ (left-singleton p e) (left′ q) = singleton-case′ p q
    singleton-case′ (left-singleton p e) (right′ q) = ⊥-elim (is-empty′ e q)
    singleton-case′ (right-singleton e p) (left′ q) = ⊥-elim (is-empty′ e q)
    singleton-case′ (right-singleton e p) (right′ q) = singleton-case′ p q

    singleton-case : Singleton x α → y ∈ α → (x ≡ y → A) → A
    singleton-case p q = singleton-case′ p (from∈ q)

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

    -- `All P α` is a first-order representation of the type `(x ∈ α) → P x`
    All : (P : @0 Name → Set) → Scope → Set
    All P ∅ = ⊤
    All P [ x ] = P x
    All P (α <> β) = All P α × All P β

    singleton-All : Singleton x α → All P α → P x
    singleton-All []-singleton p = p
    singleton-All (left-singleton s _) (ps , _) = singleton-All s ps
    singleton-All (right-singleton _ s) (_ , ps) = singleton-All s ps

    ⋈-All : α ⋈ β ≡ γ → All P γ → All P α × All P β
    ⋈-All ∅-l ps = _ , ps
    ⋈-All ∅-r ps = ps , _
    ⋈-All join ps = ps
    ⋈-All swap (ps , qs) = (qs , ps)
    ⋈-All (<>-ll q₁ q₂) ps = 
      let (ps₁ , ps₂) = ⋈-All q₂ ps
          (ps₂₁ , ps₂₂) = ⋈-All q₁ ps₂
      in (ps₁ , ps₂₁) , ps₂₂
    ⋈-All (<>-lr q₁ q₂) ps = 
      let (ps₁ , ps₂) = ⋈-All q₂ ps
          (ps₁₁ , ps₁₂) = ⋈-All q₁ ps₁
      in  (ps₁₁ , ps₂) , ps₁₂
    ⋈-All (<>-rl q₁ q₂) ps = 
      let (ps₁ , ps₂) = ⋈-All q₂ ps
          (ps₂₁ , ps₂₂) = ⋈-All q₁ ps₂
      in  ps₂₁ , (ps₁ , ps₂₂)
    ⋈-All (<>-rr q₁ q₂) ps =  
      let (ps₁ , ps₂) = ⋈-All q₂ ps
          (ps₁₁ , ps₁₂) = ⋈-All q₁ ps₁
      in  ps₁₁ , (ps₁₂ , ps₂)

    mapAll : (α : Scope) (f : ∀ {@0 x} → P x → Q x) → All P α → All Q α
    mapAll ∅ f _ = _
    mapAll [ x ] f p = f p
    mapAll (β <> γ) f (ps , qs) = (mapAll β f ps) , (mapAll γ f qs)

    tabulateAll : {α : Scope} (f : (@0 x : Name) → {{x ∈ α}} → P x) → All P α
    tabulateAll {α = ∅} f = _
    tabulateAll {α = [ x ]} f = f x {{here}}
    tabulateAll {α = β <> γ} f = tabulateAll (λ x {{p}} → f x {{left p}}) , tabulateAll (λ x {{q}} → f x {{right q}})

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
