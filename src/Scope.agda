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
open import Haskell.Prelude
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

  syntax singleton x = [ x ]

  instance
    iSemigroupScope : Semigroup (Scope name)
    iSemigroupScope = iSemigroupList

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

  syntax bind x α = x ◃ α

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

  splitEmptyLeft : {@0 β : Scope name} → empty ⋈ β ≡ β
  splitEmptyLeft = EmptyL

  {-# COMPILE AGDA2HS splitEmptyLeft #-}

  splitEmptyRight : {@0 α : Scope name} → α ⋈ empty ≡ α
  splitEmptyRight = EmptyR

  {-# COMPILE AGDA2HS splitEmptyRight #-}

  splitRefl : {@0 α β : Scope name} → Rezz _ α → α ⋈ β ≡ (α <> β)
  splitRefl (rezz []) = splitEmptyLeft
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

opaque
  unfolding bind

  splitBindLeft : {@0 α β γ : Scope name} {@0 x : name} → α ⋈ β ≡ γ → (bind x α) ⋈ β ≡ (bind x γ)
  splitBindLeft {x = x} = splitJoinLeft (rezz (singleton x))

  {-# COMPILE AGDA2HS splitBindLeft #-}

  splitBindRight : {@0 α β γ : Scope name} {@0 x : name} → α ⋈ β ≡ γ → α ⋈ (bind x β) ≡ (bind x γ)
  splitBindRight {x = x} = splitJoinRight (rezz (singleton x))

  {-# COMPILE AGDA2HS splitBindRight #-}

{-
The following statement is FALSE:
  ⋈-unique-left : α₁ ⋈ β ≡ γ → α₂ ⋈ β ≡ γ → α₁ ≡ α₂

Counterexample:

  left  left right right done : 1 2 ⋈ 1 2 ≡ 1 2 1 2
  right left left  right done : 2 1 ⋈ 1 2 ≡ 1 2 1 2

-}

opaque

  Sub : {name : Set} (@0 α β  : Scope name) → Set
  Sub α β = Σ0 _ (λ γ → α ⋈ γ ≡ β)

  {-# COMPILE AGDA2HS Sub #-}

  syntax Sub α β = α ⊆ β

  subTrans : {@0 α β γ : Scope name} → α ⊆ β → β ⊆ γ → α ⊆ γ
  subTrans < p > < q > =
    let < r , _ > = splitAssoc p q
    in  < r >

  {-# COMPILE AGDA2HS subTrans #-}

  subLeft : {@0 α β γ : Scope name} → α ⋈ β ≡ γ → α ⊆ γ
  subLeft p = < p >

  {-# COMPILE AGDA2HS subLeft transparent #-}

  subRight : {@0 α β γ : Scope name} → α ⋈ β ≡ γ → β ⊆ γ
  subRight p = < splitComm p >

  {-# COMPILE AGDA2HS subRight #-}

  subWeaken : {@0 α β : Scope name} {@0 x : name} → α ⊆ β → α ⊆ (bind x β)
  subWeaken < p > = < splitBindRight p >

  {-# COMPILE AGDA2HS subWeaken #-}

  subEmpty : {@0 α : Scope name} → empty ⊆ α
  subEmpty = subLeft splitEmptyLeft

  {-# COMPILE AGDA2HS subEmpty #-}

  subRefl : {@0 α : Scope name} → α ⊆ α
  subRefl = subLeft splitEmptyRight

  {-# COMPILE AGDA2HS subRefl #-}

  rezzSub : {@0 α β : Scope name} → α ⊆ β → Rezz _ β → Rezz _ α
  rezzSub < p > = rezzSplitLeft p

  {-# COMPILE AGDA2HS rezzSub #-}

  subJoin : {@0 α₁ α₂ β₁ β₂ : Scope name}
          → Rezz _ α₂
          → α₁ ⊆ α₂
          → β₁ ⊆ β₂
          → (α₁ <> β₁) ⊆ (α₂ <> β₂)
  subJoin r < p > < q > = < splitJoin r p q >

  {-# COMPILE AGDA2HS subJoin #-}

  subJoinKeep : {@0 α β₁ β₂ : Scope name} → Rezz _ α → β₁ ⊆ β₂ → (α <> β₁) ⊆ (α <> β₂)
  subJoinKeep r < p > = < splitJoinLeft r p >

  {-# COMPILE AGDA2HS subJoinKeep #-}

  subJoinDrop : {@0 α β₁ β₂ : Scope name} → Rezz _ α → β₁ ⊆ β₂ → β₁ ⊆ (α <> β₂)
  subJoinDrop r < p > = < splitJoinRight r p >

  {-# COMPILE AGDA2HS subJoinDrop #-}

opaque

  unfolding Sub bind

  subBindKeep : {@0 α β : Scope name} {@0 y : name} → α ⊆ β → (bind y α) ⊆ (bind y β)
  subBindKeep {y = y} = subJoinKeep (rezz (singleton y))

  {-# COMPILE AGDA2HS subBindKeep #-}

  subBindDrop : {@0 α β : Scope name} {@0 y : name} → α ⊆ β → α ⊆ (bind y β)
  subBindDrop {y = y} = subJoinDrop (rezz (singleton y))

  {-# COMPILE AGDA2HS subBindDrop #-}

opaque

  unfolding Sub

  joinSubLeft : {@0 α₁ α₂ β : Scope name} → Rezz _ α₁ → (α₁ <> α₂) ⊆ β → α₁ ⊆ β
  joinSubLeft r < p > =
    let < q , _ > = splitAssoc (splitRefl r) p
    in  < q >

  {-# COMPILE AGDA2HS joinSubLeft #-}

  joinSubRight : {@0 α₁ α₂ β : Scope name} → Rezz _ α₁ → (α₁ <> α₂) ⊆ β → α₂ ⊆ β
  joinSubRight r < p > =
    let < q , _ > = splitAssoc (splitComm (splitRefl r)) p
    in  < q >

  {-# COMPILE AGDA2HS joinSubRight #-}

In : @0 name → @0 Scope name → Set
In x α = singleton x ⊆ α

{-# COMPILE AGDA2HS In #-}

syntax In x α = x ∈ α

opaque

  unfolding bind

  coerce : {@0 α β : Scope name} {@0 x : name} → α ⊆ β → x ∈ α → x ∈ β
  coerce p q = subTrans q p

  {-# COMPILE AGDA2HS coerce #-}

  -- instance
  here : {@0 α : Scope name} {@0 x : name} → x ∈ (x ◃ α)
  here {x = x} = subLeft (splitRefl (rezz [ x ]))

  {-# COMPILE AGDA2HS here #-}

  there : {@0 α : Scope name} {@0 x y : name} → x ∈ α → x ∈ (y ◃ α)
  there = subBindDrop

  {-# COMPILE AGDA2HS there #-}

  bindSubToIn : {@0 α β : Scope name} {@0 x : name} → (x ◃ α) ⊆ β → x ∈ β
  bindSubToIn {x = x} = joinSubLeft (rezz ([ x ]))

  {-# COMPILE AGDA2HS bindSubToIn #-}

opaque

  unfolding Split Sub

  -- NOTE(flupe): cannot be compiled because no clauses

  emptyCase  : {@0 x : name} → @0 (x ∈ empty) → a
  emptyCase ()

  -- NOTE(flupe): had to erase the equality there

  singCase : {@0 x y : name} → x ∈ [ y ] → (@0 x ≡ y → a) → a
  singCase < EmptyR    > f = f refl
  singCase < ConsL _ _ > f = f refl

  {-# COMPILE AGDA2HS singCase #-}

  splitCase : {@0 α β γ : Scope name} {@0 x : name}
            → α ⋈ β ≡ γ → x ∈ γ → (x ∈ α → a) → (x ∈ β → a) → a
  splitCase EmptyL      < EmptyR     > f g = g here
  splitCase EmptyL      < ConsL x q  > f g = g here
  splitCase EmptyL      < ConsR x q  > f g = g (there < q >)
  splitCase EmptyR      < EmptyR     > f g = f here
  splitCase EmptyR      < ConsL x q  > f g = f here
  splitCase EmptyR      < ConsR x q  > f g = f (there < q >)
  splitCase (ConsL x p) < EmptyR     > f g = f here
  splitCase (ConsL x p) < ConsL .x q > f g = f here
  splitCase (ConsL x p) < ConsR .x q > f g = splitCase p < q > (f ∘ there) g
  splitCase (ConsR x p) < EmptyR     > f g = g here
  splitCase (ConsR x p) < ConsL .x q > f g = g here
  splitCase (ConsR x p) < ConsR .x q > f g = splitCase p < q > f (g ∘ there)

  {-# COMPILE AGDA2HS splitCase #-}

joinCase : {@0 α β : Scope name} {@0 x : name}
         → Rezz _ α
         → x ∈ (α <> β) → (x ∈ α → a) → (x ∈ β → a) → a
joinCase r = splitCase (splitRefl r)

{-# COMPILE AGDA2HS joinCase #-}

opaque

  unfolding Scope Sub

  -- NOTE(flupe): had to erase the equality there

  bindCase : {@0 α : Scope name} {@0 x y : name}
           → x ∈ (y ◃ α) → (@0 x ≡ y → a) → (x ∈ α → a) → a
  bindCase {y = y} p f g = joinCase (rezz [ y ]) p (λ q → (singCase q f)) g

  {-# COMPILE AGDA2HS bindCase #-}

opaque
  unfolding Split

  -- NOTE(flupe): we force the use of 2-uples instead of 3/4-uples
  --              because compilation of the latter is buggy

  splitQuad
    : {@0 α₁ α₂ β₁ β₂ γ : Scope name}
    → α₁ ⋈ α₂ ≡ γ
    → β₁ ⋈ β₂ ≡ γ
    → Σ0 ((Scope name × Scope name) × (Scope name × Scope name)) λ ((γ₁ , γ₂) , (γ₃ , γ₄)) →
        ((γ₁ ⋈ γ₂ ≡ α₁) × (γ₃ ⋈ γ₄ ≡ α₂)) ×
        ((γ₁ ⋈ γ₃ ≡ β₁) × (γ₂ ⋈ γ₄ ≡ β₂))
  splitQuad EmptyL q = < (EmptyL , q) , (EmptyL , EmptyL) >
  splitQuad EmptyR q = < (q , EmptyR) , (EmptyR , EmptyR) >
  splitQuad p EmptyL = < (EmptyL , EmptyL) , (EmptyL , p) >
  splitQuad p EmptyR = < (EmptyR , EmptyR) , (p , EmptyR) >
  splitQuad (ConsL x p) (ConsL x q) =
    let < (        r , s) , (        t , u) > = splitQuad p q
    in  < (ConsL x r , s) , (ConsL x t , u) >
  splitQuad (ConsL x p) (ConsR x q) =
    let < (        r , s) , (t ,         u) > = splitQuad p q
    in  < (ConsR x r , s) , (t , ConsL x u) >
  splitQuad (ConsR x p) (ConsL x q) =
    let < (r ,         s) , (        t , u) > = splitQuad p q
    in  < (r , ConsL x s) , (ConsR x t , u) >
  splitQuad (ConsR x p) (ConsR x q) =
    let < (r ,         s) , (t ,         u) > = splitQuad p q
    in  < (r , ConsR x s) , (t , ConsR x u) >

  {-# COMPILE AGDA2HS splitQuad #-}

{-

opaque
  unfolding Split Sub

  _⋈-≟_ : {@0 α β γ : Scope name} → (p q : α ⋈ β ≡ γ) → Dec (p ≡ q)
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
