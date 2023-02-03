
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

data _⇒_ : (@0 α β : Scope) → Set where
  ⇒weaken : α ⊆ β → α ⇒ β
  ⇒const  : Term β → α ⇒ β
  ⇒join   : α₁ ⋈ α₂ ≡ α → α₁ ⇒ β → α₂ ⇒ β → α ⇒ β

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



weaken : α ⊆ β → Term α → Term β
weakenSort : α ⊆ β → Sort α → Sort β
weakenElim : α ⊆ β → Elim α → Elim β
weakenElims : α ⊆ β → Elims α → Elims β
weakenBranch : α ⊆ β → Branch α → Branch β
weakenBranches : α ⊆ β → Branches α → Branches β
weakenEnv : β ⊆ γ → α ⇒ β → α ⇒ γ

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

weakenEnv p (⇒weaken q) = ⇒weaken (⊆-trans q p)
weakenEnv p (⇒const x) = ⇒const (weaken p x)
weakenEnv p (⇒join q f g) = ⇒join q (weakenEnv p f) (weakenEnv p g) 

liftEnv : β ⇒ γ → (α <> β) ⇒ (α <> γ)
liftEnv f = ⇒join ⋈-refl (⇒weaken (left ⊆-refl)) (weakenEnv (right ⊆-refl) f)

coerceEnv : α ⊆ β → β ⇒ γ → α ⇒ γ
coerceEnv p (⇒weaken q) = ⇒weaken (⊆-trans p q)
coerceEnv p (⇒const x) = ⇒const x
coerceEnv p (⇒join q f g) = 
  let < p₁ , p₂ , r > = ⊆-⋈-split p q
  in  ⇒join r (coerceEnv p₁ f) (coerceEnv p₂ g)

raiseEnv : α ⇒ β → (α <> β) ⇒ β
raiseEnv f = ⇒join ⋈-refl f (⇒weaken ⊆-refl)
