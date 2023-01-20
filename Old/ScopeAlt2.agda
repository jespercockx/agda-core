-- An abstract interface to representations of scopes

open import Data.Bool.Base using (Bool; true; false)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Empty
open import Data.List.Base hiding ([_])
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.DecPropositional as DecMember
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base
open import Data.Product

open import Function.Base
open import Function.Equality using (_⟶_)
open import Function.Inverse as Inv using (Inverse)
open Inverse
open import Function.HalfAdjointEquivalence using (_≃_; ↔→≃)
open _≃_

open import Relation.Nullary
open import Relation.Nullary.Decidable.Core
open import Relation.Binary using (Reflexive; Transitive)
open import Relation.Binary.PropositionalEquality.Core

module Scope where

record IScope : Set₁ where
  no-eta-equality
  field
    Scope  : Set
    Binder : Set
    Name   : Scope → Set
    _#_    : Binder → Scope → Set
    _◃_    : Binder → Scope → Scope

    nameᴮ   : ∀ {@0 α} (b : Binder) → Name (b ◃ α)
    binderᴺ : ∀ {@0 α} → Name α → Binder

    zeroᴮ   : Binder
    sucᴮ    : Binder → Binder

    _≟_     : ∀ {@0 α} (m n : Name α) → Dec (m ≡ n)

    ∅       : Scope
    ∅-equiv : Name ∅ ≃ ⊥
    _#∅     : (b : Binder) → b # ∅

    ◃-equiv : ∀ {@0 α} {b} → @0 b # α → Name (b ◃ α) ≃ (⊤ ⊎ Name α)
    suc#    : ∀ {α b} → b # α → (sucᴮ b) # (b ◃ α)

    _⊆_     : Scope → Scope → Set
    coerceᴺ : ∀ {@0 α β} → @0 α ⊆ β → Name α → Name β
    ⊆-refl  : Reflexive _⊆_
    ⊆-trans : Transitive _⊆_
    ⊆-∅     : ∀ {α} → ∅ ⊆ α
    ⊆-◃     : ∀ {α β} b → α ⊆ β → (b ◃ α) ⊆ (b ◃ β)
    ⊆-#     : ∀ {α b} → b # α → α ⊆ (b ◃ α)

{- Thought: what if we only had a type of binders that are fresh for a scope, merging the Binder and _#_ types?

Binder : Scope → Set
_▹_ : (α : Scope) → Binder α → Scope
-- (no binderᴺ function)
zeroᴮ : Binder ∅
sucᴮ  : (b : Binder α) → Binder (α ▹ b)


-}

{-
simpleScopes : IScope
simpleScopes = record { SimpleScopes }
  where module SimpleScopes where
    open DecMember Nat._≟_ using (_∈?_)

    data Fin : ℕ → Set where
      zero : {@0 n : ℕ} → Fin (suc n)
      suc  : {@0 n : ℕ} (i : Fin n) → Fin (suc n)

    Scope  : Set
    Scope = ℕ

    Binder : Set
    Binder = ⊤

    Name : Scope → Set
    Name = Fin

    _◃_ : Binder → Scope → Scope
    b ◃ α = suc α

    _#_    : Binder → Scope → Set
    b # α = ⊤

    nameᴮ   : ∀ {@0 α} (b : Binder) → Name (b ◃ α)
    nameᴮ b = zero

    binderᴺ : ∀ {@0 α} → Name α → Binder
    binderᴺ = _

    zeroᴮ  : Binder
    zeroᴮ = _

    sucᴮ  : Binder → Binder
    sucᴮ _ = _

    _≟_ : ∀ {@0 α} (m n : Name α) → Dec (m ≡ n)
    zero ≟ zero = yes refl
    zero ≟ suc n = no λ()
    suc m ≟ zero = no λ()
    suc m ≟ suc n with m ≟ n
    ... | yes refl = yes refl
    ... | no  ¬eq  = no λ { refl → ¬eq refl }

    ∅ : Scope
    ∅ = zero

    ∅-equiv : Name ∅ ≃ ⊥
    ∅-equiv = λ where
      .to               ()
      .from             ()
      .left-inverse-of  ()
      .right-inverse-of ()
      .left-right       ()

    _#∅ : (b : Binder) → b # ∅
    (b #∅) = _

    ◃-equiv : ∀ {@0 α} {b} → @0 b # α → Name (b ◃ α) ≃ (⊤ ⊎ Name α)
    ◃-equiv {α} {b} b#α = λ where
      .to zero    → inj₁ tt
      .to (suc x) → inj₂ x
      .from (inj₁ x) → zero
      .from (inj₂ y) → suc y
      .left-inverse-of zero → refl
      .left-inverse-of (suc x) → refl
      .right-inverse-of (inj₁ x) → refl
      .right-inverse-of (inj₂ y) → refl
      .left-right zero → refl
      .left-right (suc x) → refl

    suc# : ∀ {@0 α} {b} → b # α → (sucᴮ b) # (b ◃ α)
    suc# _ = tt

    _⊆_ : Scope → Scope → Set
    α ⊆ β = α ≤ β

    coerceᴺ : ∀ {@0 α β} → @0 α ⊆ β → Name α → Name β
    coerceᴺ α⊆β zero = {!!}
    coerceᴺ α⊆β (suc x) = {!!}

    ⊆-refl  : Reflexive _⊆_
    ⊆-trans : Transitive _⊆_
    ⊆-∅     : ∀ {α} → ∅ ⊆ α
    ⊆-◃     : ∀ {α β} b → α ⊆ β → (b ◃ α) ⊆ (b ◃ β)
    ⊆-#     : ∀ {α b} → b # α → α ⊆ (b ◃ α)
-}


{-
simpleScopes : IScope
simpleScopes = record { SimpleScopes }
  where module SimpleScopes where
    open DecMember Nat._≟_ using (_∈?_)

    Scope  : Set
    Scope = List ℕ

    Binder : Set
    Binder = ℕ

    data Name (s : Scope) : Set where
      _,_ : (x : ℕ) → .(x ∈ s) → Name s

    _◃_ : Binder → Scope → Scope
    b ◃ α = b ∷ α

    _#_    : Binder → Scope → Set
    b # α = ¬ (b ∈ α)

    nameᴮ   : ∀ {α} (b : Binder) → Name (b ◃ α)
    nameᴮ b = b , (here refl)

    binderᴺ : ∀ {α} → Name α → Binder
    binderᴺ (b , _) = b

    zeroᴮ  : Binder
    zeroᴮ = zero

    sucᴮ  : Binder → Binder
    sucᴮ = suc

    _≟_ : ∀ {α} (m n : Name α) → Dec (m ≡ n)
    (m , eq₁) ≟ (n , eq₂) with m Nat.≟ n
    ... | no ¬p    = no (¬p ∘ cong binderᴺ)
    ... | yes refl = yes refl

    ∅ : Scope
    ∅ = []

    ∅-equiv : Name ∅ ≃ ⊥
    ∅-equiv = λ where
      .to               (_ , ())
      .from             ()
      .left-inverse-of  (_ , ())
      .right-inverse-of ()
      .left-right       (_ , ())

    _#∅     : (b : Binder) → b # ∅
    (b #∅) ()


    ◃-equiv : ∀ {α b} → b # α → Name (b ◃ α) ≃ (⊤ ⊎ Name α)
    ◃-equiv {α} {b} b#α = ↔→≃ (Inv.inverse f {!!} {!!} {!!})
      where
        f : Name (b ◃ α) → ⊤ ⊎ Name α
        f (x , x∈b◃α) with x Nat.≟ b
        ... | yes p = inj₁ tt
        ... | no ¬p = inj₂ (x , {!!})

    suc#    : ∀ {α b} → b # α → (sucᴮ b) # (b ◃ α)
    suc# = {!!}

    _⊆_ : Scope → Scope → Set
    coerceᴺ : ∀ {α β} → α ⊆ β → Name α → Name β
    ⊆-refl  : Reflexive _⊆_
    ⊆-trans : Transitive _⊆_
    ⊆-∅     : ∀ {α} → ∅ ⊆ α
    ⊆-◃     : ∀ {α β} b → α ⊆ β → (b ◃ α) ⊆ (b ◃ β)
    ⊆-#     : ∀ {α b} → b # α → α ⊆ (b ◃ α)
-}


{- Previous attempts below

-- The basic abstract interface we use to work with variable names and
-- scopes consists of three parts:
-- 1. A set Name of names with decidable equality
-- 2. A set Scope of scopes
-- 3. A predicate _∈_ that determines when a name is in a scope
-- Note that _∈_ is a (proof-relevant) Set and not a
-- (proof-irrelevant) Prop, so it is possible for a name to be in
-- scope several times.

-- Question: currently we do not distinguish between variables that
-- are declared directly in a scope and variables that are in a scope
-- because it includes another scope. The definition of scope graphs
-- does make this distinction, I wonder whether that would be useful
-- here? One could easily have two abstract relations for "a variable
-- being declared directly" and "a scope being included", and define
-- _∈_ in terms of those two.

-- Question: should we also have a predicate _#_ that expresses a
-- variable is fresh w.r.t. a given scope, and restrict scope extension
-- to fresh variables?
-- - Advantage: guarantee no shadowing of variables, _∈_ becomes propositional,
--   can quantify over all fresh variable names in Abs constructor
--   ~> more canonical representation
-- - Disadvantage: need an additional operation to generate a fresh
--   name, need to maintain freshness proofs while doing substitution
--   or when transforming syntax

-- Important point: it would be *very* nice if we can enforce
-- statically that functions cannot distinguish alpha-equivalent
-- terms. E.g. the NomPa interface provides an abstract type Binder
-- that does not have any way to compare two binders, and a type `Name
-- α` for each world α that does have decidable equality, but only
-- between names in the same world.
--
-- Q: Do we really need separate types for binders and names to get
-- this benefit? Or can we have a single abstract type of names and
-- only allow comparison between them when they live in the same
-- world? This doesn't quite work since if we have one global type of
-- `Name`s then they can always escape their scope.
-- E.g. we could prove that `λ x. λ y. y` is distinct from `λ y. λ
-- x. x`, which we should not be able to.

-- Note: Scopes/Worlds are meant to be computationally irrelevant
-- ==> we should use run-time irrelevance for them!!!

-- Q: Should we distinguish between adding a *used* and an *unused*
-- variable to a world when extending it, as with the _+1 vs _↑1
-- operations in the NaPa approach?

record IScope : Set₁ where
  no-eta-equality
  field
    Name  : Set
    _≟_   : (m n : Name) → Dec (m ≡ n)
    Scope : Set
    _∈_   : Name → Scope → Set

open IScope {{...}} public

module _ {{iScope : IScope}} where

  -- The basic method to express properties of scopes: universal
  -- quantification over all variables in scope.
  record Forall (s : Scope) (P : (x : Name) → {{x ∈ s}} → Set) : Set where
    constructor [_]
    no-eta-equality
    field _!_ : (x : Name) {{_ : x ∈ s}} → P x

  open Forall public

  syntax Forall s (λ x → P) = ∀[ x ∈ s ] P

  record Forall! (s : Scope) (P : (x : Name) → Set) : Set where
    no-eta-equality
    field
      to   : {x : Name} → x ∈ s → P x
      from : {x : Name} → P x → x ∈ s
      linv : {x : Name} (p : x ∈ s) → from (to p) ≡ p
      rinv : {x : Name} (p : P x)   → to (from p) ≡ p
      adj  : {x : Name} (p : x ∈ s) → cong to (linv p) ≡ rinv (to p)

    instance
      foral : Forall s (λ x → P x)
      foral = [ (λ x {{p}} → to p) ]

  open Forall! public

  syntax Forall! s (λ x → P) = ∀![ x ∈ s ] P

  !_ : ∀ {s P} → {{Forall s P}} → (x : Name) {{_ : x ∈ s}} → P x
  ! x = it ! x

  Empty : (s : Scope) → Set
  Empty s = ∀[ x ∈ s ] ⊥

  Singleton : (s : Scope) (x : Name) → Set
  Singleton s x = ∀[ y ∈ s ] (x ≡ y)

  Split : (s s₁ s₂ : Scope) → Set
  Split s s₁ s₂ = ∀[ x ∈ s ] (x ∈ s₁ ⊎ x ∈ s₂)

  Split! : (s s₁ s₂ : Scope) → Set
  Split! s s₁ s₂ = ∀![ x ∈ s ] (x ∈ s₁ ⊎ x ∈ s₂)

  Split₁ : (s s₁ : Scope) (x : Name) → Set
  Split₁ s s₁ x = ∀[ y ∈ s ] (y ∈ s₁ ⊎ x ≡ y)

  Split₁! : (s s₁ : Scope) (x : Name) → Set
  Split₁! s s₁ x = ∀![ y ∈ s ] (y ∈ s₁ ⊎ x ≡ y)

  _⊑_ : (s s' : Scope) → Set
  s ⊑ s' = ∀[ x ∈ s ] (x ∈ s')

  instance
    ⊑-refl : {s : Scope} → s ⊑ s
    ⊑-refl = [ (λ _ → it) ]

  ⊑-trans : {s s' s'' : Scope} → s ⊑ s' → s' ⊑ s'' → s ⊑ s''
  ⊑-trans p q = [ (λ x → (q ! x) {{p ! x}}) ]

  ⊑-split₁ : {s s₁ s₂ : Scope} {x : Name} → s ⊑ s' → Split₁


  -- Here is a different way to express the separation of a scope into
  -- two disjoint parts as a universal property:
  Split' : (s s₁ s₂ : Scope) → Set
  Split' s s₁ s₂ = ∀ s' → {{s₁ ⊑ s'}} → {{s₂ ⊑ s'}} → s ⊑ s'

  -- It is implied by the variant defined above:
  Split→Split' : ∀ {s s₁ s₂} → Split s s₁ s₂ → Split' s s₁ s₂
  Split→Split' f s' =
    [ (λ x → case f ! x of λ where
      (inj₁ y) → (! x) {{y}}
      (inj₂ z) → (! x) {{z}})
    ]

  -- However the opposite direction doesn't go through since there is
  -- no concrete way of constructing a union of two scopes using the
  -- abstract interface defined above.
  -- Split'→Split : ∀ {s s₁ s₂} → Split' s s₁ s₂ → Split s s₁ s₂
  -- Split'→Split f = [ (λ x → {!Split'!}) ]

  -- This seems to suggest that some kind of existence property is
  -- still missing from the abstract interface. It is not a problem as
  -- long as you program against the abstract interface (since you are
  -- forced to take all possible implementations into account), but it
  -- might be worth it to make it explicit.

  -- On the other hand, working with Split is not so nice when we want
  -- to implement weakening. In particular, when we want to

-}

{-
    -- Question: currently each of the structures on scopes defined
    -- below is given as an abstract type + an equivalence with a
    -- concrete type. Does this actually buy us something compared
    -- to just defining the structure directly as that type?

    _⊑_      : Scope → Scope → Set
    equivSub : ∀ {s s'} → (s ⊑ s') ≃ (∀ x → {{x ∈ s}} → x ∈ s')

    Empty      : Scope → Set
    equivEmpty : ∀ {s x} → {{Empty s}} → (x ∈ s) ≃ ⊥


    --Split      : Scope → Scope → Scope → Set
    --equivSplit : ∀ {s s₁ s₂ x} → {{Split s s₁ s₂}}
    --           → (x ∈ s) ≃ (x ∈ s₁ ⊎ x ∈ s₂)

    Forall      : (s : Scope) → (∀ x → {{x ∈ s}} → Set) → Set
    equivForall : ∀ {s} {P : ∀ x → {{x ∈ s}} → Set}
                → Forall s P ≃ (∀ x {{_ : x ∈ s}} → P x)
-}

{-
  sub : ∀ {s s'} → {{s ⊑ s'}}
      → ∀ x → {{x ∈ s}} → x ∈ s'
  sub = to equivSub it

  fromEmpty : ∀ {s x} → {{Empty s}} → {{x ∈ s}} → ⊥
  fromEmpty = to equivEmpty it
-}

{-
  fromSplit : ∀ {s s₁ s₂ x} → {{Split s s₁ s₂}}
            → {{x ∈ s}} → x ∈ s₁ ⊎ x ∈ s₂
  fromSplit = to equivSplit it

  toSplitL : ∀ {s s₁ s₂ x} → {{Split s s₁ s₂}}
            → {{x ∈ s₁}} → x ∈ s
  toSplitL = from equivSplit (inj₁ it)

  toSplitR : ∀ {s s₁ s₂ x} → {{Split s s₁ s₂}}
            → {{x ∈ s₂}} → x ∈ s
  toSplitR = from equivSplit (inj₂ it)
-}

{-
  pack  : ∀ {s P} → (∀ x {{_ : x ∈ s}} → P x) → Forall s P
  pack = from equivForall

  apply : ∀ {s P} → Forall s P → ∀ x {{_ : x ∈ s}} → P x
  apply = to equivForall
-}


{-


record IScope : Set₁ where
  no-eta-equality
  field
    Scope  : Set
    Var    : Scope → Set

    empty  : Scope
    is-empty : Var empty → ⊥

    single  : Name → Scope
    here    : (x : Name) → Var (single x)
    is-here : ∀ {x} → (v : Var (single x)) → v ≡ here x

    join   : Scope → Scope → Scope
    left   : ∀ {l r} → Var l → Var (join l r)
    right  : ∀ {l r} → Var r → Var (join l r)
    left-or-right : ∀ {l r} → (v : Var (join l r)) → Var l ⊎ Var r
    is-left-or-right : ∀ {l r} → (v : Var (join l r)) →
      case left-or-right v of λ where
        (inj₁ x) → v ≡ left x
        (inj₂ y) → v ≡ right y

    ForAll : (s : Scope) → (Var s → Set) → Set
    pack  : ∀ {s P} → ((x : Var s) → P x) → ForAll s P
    apply : ∀ {s P} → ForAll s P → (x : Var s) → P x

  extend : Name → Scope → Scope
  extend x s = join (single x) s

  extends : List Name → Scope → Scope
  extends []       s = s
  extends (x ∷ xs) s = extend x (extends xs s)

  vars : List Name → Scope
  vars xs = extends xs empty

  shuffle : ∀ {s₁ s₂ s₃} → Var (join s₁ (join s₂ s₃)) → Var (join s₂ (join s₁ s₃))
  shuffle x = case left-or-right x of λ where
    (inj₁ y) → right (left y)
    (inj₂ z) → case left-or-right z of λ where
      (inj₁ v) → left v
      (inj₂ w) → right (right w)

  rotate : ∀ {s₁ s₂ s₃} → Var (join s₁ (join s₂ s₃)) → Var (join (join s₁ s₂) s₃)
  rotate x = case left-or-right x of λ where
    (inj₁ y) → left (left y)
    (inj₂ z) → case left-or-right z of λ where
      (inj₁ v) → left (right v)
      (inj₂ w) → right w

  variable s s' s'' s₀ s₁ s₂ s₃ : Scope

-}
