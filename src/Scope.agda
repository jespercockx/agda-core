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
open import Utils.Erase
open import Haskell.Prim
open import Haskell.Prim.Tuple
open import Haskell.Prim.List
open import Haskell.Law.Equality
import Haskell.Law.List as List

module Scope where

private variable
  A B C name    : Set
  @0 P Q R      : @0 A → Set
  @0 α β γ α₁ α₂ β₁ β₂     : List (Erase name)

opaque

  Scope : (name : Set) → Set
  Scope name = List (Erase name)

  {-# COMPILE AGDA2HS Scope #-}

  empty : Scope name
  empty = []

  {-# COMPILE AGDA2HS empty #-}
  
  singleton : @0 name → Scope name
  singleton x = Erased x ∷ []

  {-# COMPILE AGDA2HS singleton #-}

  _<>_ : Scope name → Scope name → Scope name
  _<>_ = _++_

  {-# COMPILE AGDA2HS _<>_ #-}

  -- properties (not compiled)
  ----------------------------

  <>-∅ : {α : Scope name} → α <> empty ≡ α
  <>-∅ = List.++-[] _

  ∅-<> : {α : Scope name} → empty <> α ≡ α
  ∅-<> = refl

  <>-assoc : {α β γ : Scope name} → (α <> β) <> γ ≡ α <> (β <> γ)
  <>-assoc {α = []} = refl
  <>-assoc {α = x ∷ α} = cong (x ∷_) (<>-assoc {α = α})

  ---------------------------

  bind : @0 name → Scope name → Scope name
  bind x α = singleton x <> α

  {-# COMPILE AGDA2HS bind #-}

-- This datatype has to use the actual [] and _∷_ constructors instead of
-- ∅ and _◃_, because otherwise the erased constructor arguments are not
-- recognized as being forced (see https://github.com/agda/agda/issues/6744).

data Join {name : Set} : (@0 α β γ : List (Erase name)) → Set where
  EmptyL : Join [] β β
  EmptyR : Join α [] α
  ConsL  : (@0 x : name) → Join α β γ → Join (Erased x ∷ α) β (Erased x ∷ γ)
  ConsR  : (@0 y : name) → Join α β γ → Join α (Erased y ∷ β) (Erased y ∷ γ)

{-# COMPILE AGDA2HS Join #-}

opaque
  unfolding Scope

  -- OPI (Order-Preserving Interleaving)
  Split : (@0 α β γ : Scope name) → Set
  Split = Join

  {-# COMPILE AGDA2HS Split #-}

  syntax Split α β γ = α ⋈ β ≡ γ

opaque
  unfolding Split

  splitLeft : {@0 β : Scope name} → empty ⋈ β ≡ β
  splitLeft = EmptyL

  {-# COMPILE AGDA2HS splitLeft #-}

  splitRight : {@0 α : Scope name} → α ⋈ empty ≡ α
  splitRight = EmptyR

  {-# COMPILE AGDA2HS splitRight #-}

  splitRefl : {@0 α β : Scope name} → Rezz _ α → α ⋈ β ≡ (α <> β)
  splitRefl (rezz []) = splitLeft
  splitRefl (rezz (Erased x ∷ α)) = ConsL x (splitRefl (rezz α))

  {-# COMPILE AGDA2HS splitRefl #-}

opaque
  unfolding Split

  splitComm : {@0 α β γ : Scope name} → α ⋈ β ≡ γ → β ⋈ α ≡ γ
  splitComm EmptyL = EmptyR
  splitComm EmptyR = EmptyL
  splitComm (ConsL x p) = ConsR x (splitComm p)
  splitComm (ConsR y p) = ConsL y (splitComm p)

  {-# COMPILE AGDA2HS splitComm #-}

opaque
  unfolding Split

  splitAssoc : {@0 α β γ δ ε : Scope name}
          → α ⋈ β ≡ γ
          → γ ⋈ δ ≡ ε
          → Σ0 _ λ ζ → (α ⋈ ζ ≡ ε) × (β ⋈ δ ≡ ζ)
  splitAssoc EmptyL q = < EmptyL , q >
  splitAssoc EmptyR q = < q , EmptyL >
  splitAssoc p EmptyR = < p , EmptyR >
  splitAssoc (ConsL x p) (ConsL .x q) =
    let < r , s > = splitAssoc p q
    in  < ConsL x r , s >
  splitAssoc (ConsR y p) (ConsL .y q) =
    let < r , s > = splitAssoc p q
    in  < ConsR y r , ConsL y s >
  splitAssoc p (ConsR y q) =
    let < r , s > = splitAssoc p q
    in  < ConsR y r , ConsR y s >

  {-# COMPILE AGDA2HS splitAssoc #-}

opaque
  unfolding Split

  private
    rezzBind : {@0 α : Scope name} {@0 x : name} → Rezz _ α → Rezz _ (bind x α)
    rezzBind {name = name} = rezzCong2 _∷_ (rezzErase {a = name})

    {-# COMPILE AGDA2HS rezzBind #-}

  rezzSplit : {@0 α β γ : Scope name} → Split α β γ → Rezz _ γ → Rezz _ α × Rezz _ β
  rezzSplit EmptyL r = rezz empty , r
  rezzSplit EmptyR r = r , rezz empty
  rezzSplit (ConsL x p) r =
    let (r1 , r2) = rezzSplit p (rezzTail r)
    in  (rezzBind r1) , r2
  rezzSplit (ConsR x p) r =
    let (r1 , r2) = rezzSplit p (rezzTail r)
    in  r1 , rezzBind r2

  {-# COMPILE AGDA2HS rezzSplit #-}

  rezzSplitLeft : {@0 α β γ : Scope name} → α ⋈ β ≡ γ → Rezz _ γ → Rezz _ α
  rezzSplitLeft p r = fst (rezzSplit p r)

  {-# COMPILE AGDA2HS rezzSplitLeft #-}

  rezzSplitRight : {@0 α β γ : Scope name} → α ⋈ β ≡ γ → Rezz _ γ → Rezz _ β
  rezzSplitRight p r = snd (rezzSplit p r)

  {-# COMPILE AGDA2HS rezzSplitRight #-}

  -- NOTE(flupe): making Rezz explicit for now
  splitJoinLeft : {@0 α β β₁ β₂ : Scope name}
                → Rezz _ α
                → β₁ ⋈ β₂ ≡ β
                → (α <> β₁) ⋈ β₂ ≡ (α <> β)
  splitJoinLeft (rezz []) p = p
  splitJoinLeft (rezz (Erased x ∷ α)) p = ConsL x (splitJoinLeft (rezz α) p)

  {-# COMPILE AGDA2HS splitJoinLeft #-}

  splitJoinRight : {@0 α β β₁ β₂ : Scope name}
                 → Rezz _ α
                 → β₁ ⋈ β₂ ≡ β
                 → β₁ ⋈ (α <> β₂) ≡ (α <> β)
  splitJoinRight (rezz []) p = p
  splitJoinRight (rezz (Erased x ∷ α)) p = ConsR x (splitJoinRight (rezz α) p)

  {-# COMPILE AGDA2HS splitJoinRight #-}

  splitJoin : {@0 α α₁ α₂ β β₁ β₂ : Scope name}
            → Rezz _ α
            → α₁ ⋈ α₂ ≡ α
            → β₁ ⋈ β₂ ≡ β
            → (α₁ <> β₁) ⋈ (α₂ <> β₂) ≡ (α <> β)
  splitJoin r EmptyL      q = splitJoinRight r q
  splitJoin r EmptyR      q = splitJoinLeft  r q
  splitJoin r (ConsL x p) q = ConsL x (splitJoin (rezzTail r) p q)
  splitJoin r (ConsR x p) q = ConsR x (splitJoin (rezzTail r) p q)

  {-# COMPILE AGDA2HS splitJoin #-}
{-


opaque
  ⋈-◃-left : α ⋈ β ≡ γ → (x ◃ α) ⋈ β ≡ (x ◃ γ)
  ⋈-◃-left = ⋈-<>-left

  ⋈-◃-right : α ⋈ β ≡ γ → α ⋈ (x ◃ β) ≡ (x ◃ γ)
  ⋈-◃-right = ⋈-<>-right

{-
The following statement is FALSE:
  ⋈-unique-left : α₁ ⋈ β ≡ γ → α₂ ⋈ β ≡ γ → α₁ ≡ α₂

Counterexample:

  left  left right right done : 1 2 ⋈ 1 2 ≡ 1 2 1 2
  right left left  right done : 2 1 ⋈ 1 2 ≡ 1 2 1 2

-}


opaque
  @0 _⊆_ : (α β  : Scope) → Set
  α ⊆ β = Σ0 Scope (λ γ → α ⋈ γ ≡ β)

  ⊆-trans : α ⊆ β → β ⊆ γ → α ⊆ γ
  ⊆-trans < p > < q > =
    let < r , _ > = ⋈-assoc p q
    in  < r >

  ⊆-left : α ⋈ β ≡ γ → α ⊆ γ
  ⊆-left p = < p >

  ⊆-right : α ⋈ β ≡ γ → β ⊆ γ
  ⊆-right p = < ⋈-comm p >

  ⊆-weaken : α ⊆ β → α ⊆ (x ◃ β)
  ⊆-weaken < p > = < ⋈-◃-right p >

  ⊆-∅ : ∅ ⊆ α
  ⊆-∅ = ⊆-left ⋈-∅-left

  ⊆-refl : α ⊆ α
  ⊆-refl = ⊆-left ⋈-∅-right

  rezz-⊆ : α ⊆ β → Rezz β → Rezz α
  rezz-⊆ < p > = rezz-⋈-left p

  ⊆-<> : {{Rezz α₂}} → α₁ ⊆ α₂ → β₁ ⊆ β₂ → (α₁ <> β₁) ⊆ (α₂ <> β₂)
  ⊆-<> {{r}} < p > < q > = < ⋈-<> {{r}} p q >

  ⊆-<>-keep : {{Rezz α}} → β₁ ⊆ β₂ → (α <> β₁) ⊆ (α <> β₂)
  ⊆-<>-keep {{r}} < p > = < ⋈-<>-left {{r}} p >

  ⊆-<>-drop : {{Rezz α}} → β₁ ⊆ β₂ → β₁ ⊆ (α <> β₂)
  ⊆-<>-drop {{r}} < p > = < ⋈-<>-right {{r}} p >

  ⊆-◃-keep  : α ⊆ β → (y ◃ α) ⊆ (y ◃ β)
  ⊆-◃-keep = ⊆-<>-keep

  ⊆-◃-drop  : α ⊆ β → α ⊆ (y ◃ β)
  ⊆-◃-drop = ⊆-<>-drop

  -- The instance argument here should be resolved automatically,
  -- but currently it is not because of Agda issue #5703.
  <>-⊆-left : {{Rezz α₁}} → (α₁ <> α₂) ⊆ β → α₁ ⊆ β
  <>-⊆-left {{r}} < p > =
    let < q , _ > = ⋈-assoc (⋈-refl {{r}}) p
    in  < q >

  <>-⊆-right : {{Rezz α₁}} → (α₁ <> α₂) ⊆ β → α₂ ⊆ β
  <>-⊆-right {{r}} < p > =
    let < q , _ > = ⋈-assoc (⋈-comm (⋈-refl {{r}})) p
    in  < q >


@0 _∈_ : @0 Name → Scope → Set
x ∈ α = [ x ] ⊆ α


opaque
  coerce : α ⊆ β → x ∈ α → x ∈ β
  coerce p q = ⊆-trans q p

  instance
    here : x ∈ (x ◃ α)
    here = ⊆-left ⋈-refl

  there : x ∈ α → x ∈ (y ◃ α)
  there = ⊆-◃-drop

  ◃-⊆-to-∈ : (x ◃ α) ⊆ β → x ∈ β
  ◃-⊆-to-∈ = <>-⊆-left

opaque
  unfolding _⋈_≡_ _⊆_

  ∅-case  : @0 (x ∈ ∅) → A
  ∅-case ()

  []-case : x ∈ [ y ] → (x ≡ y → A) → A
  []-case < EmptyR    > f = f refl
  []-case < ConsL _ _ > f = f refl

  ⋈-case : α ⋈ β ≡ γ → x ∈ γ → (x ∈ α → A) → (x ∈ β → A) → A
  ⋈-case EmptyL      < EmptyR     > f g = g here
  ⋈-case EmptyL      < ConsL x q  > f g = g here
  ⋈-case EmptyL      < ConsR x q  > f g = g (there < q >)
  ⋈-case EmptyR      < EmptyR     > f g = f here
  ⋈-case EmptyR      < ConsL x q  > f g = f here
  ⋈-case EmptyR      < ConsR x q  > f g = f (there < q >)
  ⋈-case (ConsL x p) < EmptyR     > f g = f here
  ⋈-case (ConsL x p) < ConsL .x q > f g = f here
  ⋈-case (ConsL x p) < ConsR .x q > f g = ⋈-case p < q > (f ∘ there) g
  ⋈-case (ConsR x p) < EmptyR     > f g = g here
  ⋈-case (ConsR x p) < ConsL .x q > f g = g here
  ⋈-case (ConsR x p) < ConsR .x q > f g = ⋈-case p < q > f (g ∘ there)

<>-case : {{Rezz α}} → x ∈ (α <> β) → (x ∈ α → A) → (x ∈ β → A) → A
<>-case {{r}} = ⋈-case (⋈-refl {{r}})

opaque
  unfolding Scope _⊆_

  ◃-case : x ∈ (y ◃ α) → (x ≡ y → A) → (x ∈ α → A) → A
  ◃-case p f g = <>-case p (λ q → ([]-case q f)) g

opaque
  unfolding _⋈_≡_

  ⋈-quad : α₁ ⋈ α₂ ≡ γ → β₁ ⋈ β₂ ≡ γ
          → Σ0 (Scope × Scope × Scope × Scope) λ (γ₁ , γ₂ , γ₃ , γ₄) →
            (γ₁ ⋈ γ₂ ≡ α₁) × (γ₃ ⋈ γ₄ ≡ α₂) ×
            (γ₁ ⋈ γ₃ ≡ β₁) × (γ₂ ⋈ γ₄ ≡ β₂)
  ⋈-quad EmptyL q = < EmptyL , q , EmptyL , EmptyL >
  ⋈-quad EmptyR q = < q , EmptyR , EmptyR , EmptyR >
  ⋈-quad p EmptyL = < EmptyL , EmptyL , EmptyL , p >
  ⋈-quad p EmptyR = < EmptyR , EmptyR , p , EmptyR >
  ⋈-quad (ConsL x p) (ConsL x q) =
    let <         r , s ,         t , u > = ⋈-quad p q
    in  < ConsL x r , s , ConsL x t , u >
  ⋈-quad (ConsL x p) (ConsR x q) =
    let <         r , s , t ,         u > = ⋈-quad p q
    in  < ConsR x r , s , t , ConsL x u >
  ⋈-quad (ConsR x p) (ConsL x q) =
    let < r ,         s ,         t , u > = ⋈-quad p q
    in  < r , ConsL x s , ConsR x t , u >
  ⋈-quad (ConsR x p) (ConsR x q) =
    let < r ,         s , t ,         u > = ⋈-quad p q
    in  < r , ConsR x s , t , ConsR x u >

opaque
  unfolding _⋈_≡_ _⊆_

  _⋈-≟_ : (p q : α ⋈ β ≡ γ) → Dec (p ≡ q)
  EmptyL     ⋈-≟ EmptyL    = yes refl
  EmptyR     ⋈-≟ EmptyR    = yes refl
  ConsL x p  ⋈-≟ ConsL x q = Dec.map (cong (ConsL x)) (λ where refl → refl) (p ⋈-≟ q)
  ConsR x p  ⋈-≟ ConsR x q = Dec.map (cong (ConsR x)) (λ where refl → refl) (p ⋈-≟ q)
  EmptyL     ⋈-≟ EmptyR    = no λ ()
  EmptyL     ⋈-≟ ConsR y q = no λ ()
  EmptyR     ⋈-≟ EmptyL    = no λ ()
  EmptyR     ⋈-≟ ConsL x q = no λ ()
  ConsL x p  ⋈-≟ EmptyR    = no λ ()
  ConsL x p  ⋈-≟ ConsR x q = no λ ()
  ConsR x p  ⋈-≟ EmptyL    = no λ ()
  ConsR x p  ⋈-≟ ConsL x q = no λ ()

  private
    ∅-⋈-injective : ∅ ⋈ α ≡ β → α ≡ β
    ∅-⋈-injective EmptyL = refl
    ∅-⋈-injective EmptyR = refl
    ∅-⋈-injective (ConsR x p) = cong (_ ∷_) (∅-⋈-injective p)

  -- TODO: clean up this horrible mess of a definition
  _∈-≟_ : (p : x ∈ α) (q : y ∈ α)
    → Dec (_≡_ {A = Σ0 Name (_∈ α)} (erase x , p) (erase y , q))
  < EmptyR > ∈-≟ < EmptyR > = yes refl
  < EmptyR > ∈-≟ < ConsL x q > = no λ ()
  < ConsL x p > ∈-≟ < EmptyR > = no λ ()
  < ConsL x p > ∈-≟ < ConsL x q > =
    case trans (∅-⋈-injective p) (sym (∅-⋈-injective q)) of λ where
      refl → Dec.map (cong (λ r → erase _ , erase _ , ConsL x r))
                     (λ where refl → refl)
                     (p ⋈-≟ q)
  < ConsL x p > ∈-≟ < ConsR x q > = no λ ()
  < ConsR x p > ∈-≟ < ConsL x q > = no λ ()
  < ConsR x p > ∈-≟ < ConsR x q > = Dec.map aux (λ where refl → refl) (< p > ∈-≟ < q >)
    where
      aux : ∀ {@0 x y α β γ} {p : Join [ x ] α γ} {q : Join [ y ] β γ} →
            _≡_ {A = Σ0 Name (_∈ γ)} (erase x , erase α , p) (erase y , erase β , q) →
            _≡_ {A = Σ0 Name (_∈ (erase z ∷ γ))} (erase x , erase (erase z ∷ α) , ConsR z p) (erase y , erase (erase z ∷ β) , ConsR z q)
      aux refl = refl

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
  unfolding Scope

  All : (P : @0 Name → Set) → Scope → Set
  All P = List.All λ x → P (get x)

  All∅ : All P ∅
  All∅ = []

  All[] : P x → All P [ x ]
  All[] p = p ∷ []

  getAll[] : All P [ x ] → P x
  getAll[] (p ∷ []) = p

  All<> : All P α → All P β → All P (α <> β)
  All<> [] pbs = pbs
  All<> (px ∷ pas) pbs = px ∷ All<> pas pbs


opaque
  unfolding Empty _⋈_≡_

  emptyAll : Empty α → All P α
  emptyAll < EmptyL > = All∅
  emptyAll < EmptyR > = All∅

opaque
  unfolding All _⊆_ _⋈_≡_

  lookupAll : All P α → x ∈ α → P x
  lookupAll ps < EmptyR    > = getAll[] ps
  lookupAll ps < ConsL x _ > = case ps of λ where
    (px ∷ _ ) → px
  lookupAll ps < ConsR x q > = case ps of λ where
    (_  ∷ ps) → lookupAll ps < q >

_!_ : All P α → (@0 x : Name) → {@(tactic auto) _ : x ∈ α} → P x
(ps ! _) {s} = lookupAll ps s

opaque
  unfolding All

  mapAll : (f : ∀ {@0 x} → P x → Q x) → All P α → All Q α
  mapAll f [] = []
  mapAll f (p ∷ ps) = f p ∷ mapAll f ps

  tabulateAll : {{Rezz α}} → (f : ∀ {@0 x} → (x ∈ α) → P x) → All P α
  tabulateAll {{rezz []}} f = []
  tabulateAll {{rezz (x ∷ α)}} f = f here ∷ tabulateAll {{rezz α}} (f ∘ there)

opaque
  unfolding All _⋈_≡_

  splitAll : α ⋈ β ≡ γ → All P γ → All P α × All P β
  splitAll EmptyL ps = [] , ps
  splitAll EmptyR ps = ps , []
  splitAll (ConsL x q) (p ∷ ps) = Product.map₁ (p ∷_) (splitAll q ps)
  splitAll (ConsR x q) (p ∷ ps) = Product.map₂ (p ∷_) (splitAll q ps)


-}
