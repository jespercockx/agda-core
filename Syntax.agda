
open import Utils

open import Scope

open import Data.Nat.Base

module Syntax 
    {Name     : Set} 
    (iScope   : IScope Name) (let open IScope iScope) 
    (defs     : Scope)
    (cons     : Scope)
    (conArity : All (λ _ → Scope) cons) 
  where

data Term  (@0 α : Scope) : Set
data Sort  (@0 α : Scope) : Set
data Elim  (@0 α : Scope) : Set
data Elims (@0 α : Scope) : Set
data Branch (@0 α : Scope) : Set
data Branches (@0 α : Scope) : Set

-- Design choice: no separate syntactic class for types. Everything
-- is just a term or a sort.
Type = Term

_⇒_ : (α β : Scope) → Set
α ⇒ β = All (λ _ → Term β) α

{-# NO_POSITIVITY_CHECK #-} -- silly Agda
data Term α where
  var    : (@0 x : Name) → {{x ∈ α}} → Term α
  def    : (@0 d : Name) → {{d ∈ defs}} → Term α
  -- constructors should be fully applied
  con    : (@0 c : Name) → {{_ : c ∈ cons}} → ((conArity ! c) ⇒ α) → Term α
  lam    : (@0 x : Name) (v : Term (x ◃ α)) → Term α
  appE   : (v : Term α) (es : Elims α) → Term α
  pi     : (@0 x : Name) (a : Term α) (b : Term (x ◃ α)) → Term α
  sort   : Sort α → Term α
  let′   : (@0 x : Name) (u : Term α) (v : Term (x ◃ α)) → Term α
  case   : (@0 x : Name) {{x∈α : x ∈ α}} (bs : Branches (diff x∈α)) → Term α
  error  : Term α -- Needed to define substitution
  -- TODO: literals

data Sort α where
  type : ℕ → Sort α -- TODO: universe polymorphism

data Elim α where
  arg  : Term α → Elim α
  proj : (x : Name) → {{x ∈ defs}} → Elim α

data Elims α where
  []  : Elims α
  _∷_ : Elim α → Elims α → Elims α

_++E_ : Elims α → Elims α → Elims α
[]       ++E ys = ys
(x ∷ xs) ++E ys = x ∷ (xs ++E ys)

data Branch α where
  branch : (@0 c : Name) → {{_ : c ∈ cons}} → Term ((conArity ! c) <> α) → Branch α

data Branches α where
  []  : Branches α
  _∷_ : Branch α → Branches α → Branches α

apply : Term α → Term α → Term α
apply u v = appE u (arg v ∷ [])

elimView : Term α → Term α × Elims α
elimView (appE u es₂) = 
  let (u' , es₁) = elimView u
  in  u' , (es₁ ++E es₂)
elimView u = u , []

coerceEnv : {α : Scope} → α ⊆ β → β ⇒ γ → α ⇒ γ
coerceEnv σ f = tabulateAll λ x → (f ! x) {{coerce σ it}}

{-# TERMINATING #-} -- silly Agda
weaken : α ⊆ β → Term α → Term β
weakenSort : α ⊆ β → Sort α → Sort β
weakenElim : α ⊆ β → Elim α → Elim β
weakenElims : α ⊆ β → Elims α → Elims β
weakenBranch : α ⊆ β → Branch α → Branch β
weakenBranches : α ⊆ β → Branches α → Branches β
weakenEnv : {α : Scope} → β ⊆ γ → α ⇒ β → α ⇒ γ

weaken p (var x {{q}})     = var x {{coerce p q}}
weaken p (def f)           = def f 
weaken p (con c vs)        = con c (weakenEnv p vs)
weaken p (lam x v)         = lam x (weaken (⊆-◃ p) v)
weaken p (appE u es)       = appE (weaken p u) (weakenElims p es)
weaken p (pi x a b)        = pi x (weaken p a) (weaken (⊆-◃ p) b)
weaken p (sort α)          = sort (weakenSort p α)
weaken p (let′ x v t)      = let′ x (weaken p v) (weaken (⊆-◃ p) t)
weaken p (case x {{q}} bs) = case x {{coerce p q}} (weakenBranches (diff-⊆-trans q p) bs)
weaken p error             = error

weakenSort p (type x) = type x

weakenElim p (arg x)  = arg (weaken p x)
weakenElim p (proj x) = proj x

weakenElims p []       = []
weakenElims p (e ∷ es) = weakenElim p e ∷ weakenElims p es

weakenBranch p (branch c x) = branch c (weaken (⊆-<> p) x)

weakenBranches p []       = []
weakenBranches p (b ∷ bs) = weakenBranch p b ∷ weakenBranches p bs

weakenEnv σ f = mapAll _ (weaken σ) f --weaken σ (f x)


liftEnv : {α β : Scope} → β ⇒ γ → (α <> β) ⇒ (α <> γ)
liftEnv f = tabulateAll λ x {{p}} → <>-case p 
  (λ q → var _ {{coerce (left ⊆-refl) q}}) 
  λ q →  weaken (right ⊆-refl) ((f ! _) {{q}})

raiseEnv : {α β : Scope} → α ⇒ β → (α <> β) ⇒ β
raiseEnv f = tabulateAll λ x {{p}} → <>-case p 
  (λ  q → (f ! x) {{q}})
  (λ q → var x {{q}})


{- OUTDATED COMMENT
Below is an attempt at an alternative representation of
abstractions.
record Abs s x where
  inductive
  constructor abs
  field
    unAbs : ∀ {s'} → {{α ⊆ β}} → {{x ∈ s'}} → Term s'

Env : (s s' : Scope) → Set
Env s s' = ∀[ x ∈ s ] (Term s')

-- The above encodes the body of an abstraction as a term that works
-- in *every* scope that includes at least the bound variable as well
-- as the scope of the term itself.  This seems correct, but is this
-- the best way to encode it? An alternative way would be to work with
-- an explicit 'split' of a scope into two scopes, e.g. using the type
--
-- Split s s₁ s₂ = ∀[ x ∈ s ] (x ∈ s₁ ⊎ x ∈ s₂)
--
-- The Split type seems to be a more direct approach, but it soon runs
-- into hairy issues with having to explicitly use associativity and
-- commutativity of ⊎, e.g. when implementing weakening. In contrast,
-- with our more abstract representation weakening is rather easy:

-- So we run into trouble with implementing substitution under a
-- binder. The cause is our inability to construct a new scope that
-- includes both s and the variable x. Is it a bug or a feature?

substAbs {s = s} {s' = s'} σ x (abs u) =
  abs λ {s''} {{s'⊆s''}} {{x∈s''}} → {!u!} --subst {s} {s''} (weakenEnv {!!} σ) {!u!}
-}
