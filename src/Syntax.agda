open import Haskell.Prelude hiding (All)
open import Scope
open import Utils.Tactics using (auto)
open import Utils.Erase

module Syntax
  {@0 name     : Set}
  (@0 defs     : Scope name)
  (@0 cons     : Scope name)
  (@0 conArity : All (λ _ → Scope name) cons)
  where

data Term (@0 α : Scope name) : Set
data Sort (@0 α : Scope name) : Set
data Elim (@0 α : Scope name) : Set
Elims : (@0 α : Scope name) → Set
data Branch (@0 α : Scope name) : Set
Branches : (@0 α : Scope name) → Set

-- Design choice: no separate syntactic class for types. Everything
-- is just a term or a sort.
Type = Term
{-# COMPILE AGDA2HS Type #-}

data Subst : (@0 α β : Scope name) → Set where
  SNil  : {@0 β : Scope name} → Subst empty β
  SCons : {@0 α β : Scope name} {@0 x : name} → Term β → Subst α β → Subst (x ◃ α) β
{-# COMPILE AGDA2HS Subst #-}

syntax Subst α β = α ⇒ β

-- This should ideally be the following:
--_⇒_ : (α β : Scope) → Set
--α ⇒ β = All (λ _ → Term β) α
-- but this would require a strict positivity annotation on All
-- TODO: is this because All is opaque?

data Term α where
  -- NOTE(flupe): removed tactic arguments for now because hidden arguments not supported yet #217
  TVar  : (@0 x : name) → x ∈ α → Term α
  TDef  : (@0 d : name) → d ∈ defs → Term α
  TCon  : (@0 c : name) (c∈cons : c ∈ cons) → (lookupAll conArity c∈cons) ⇒ α → Term α
  TLam  : (@0 x : name) (v : Term (x ◃ α)) → Term α
  TApp  : (u : Term α) (es : Elims α) → Term α
  TPi   : (@0 x : name) (u : Term α) (v : Term (x ◃ α)) → Term α
  TSort : Sort α → Term α
  TLet  : (@0 x : name) (u : Term α) (v : Term (x ◃ α)) → Term α
  -- TODO: literals
  -- TODO: constructor for type annotation
{-# COMPILE AGDA2HS Term     #-}

data Sort α where
  STyp : Nat → Sort α -- TODO: universe polymorphism
{-# COMPILE AGDA2HS Sort     #-}

data Elim α where
  EArg  : Term α → Elim α
  EProj : (@0 x : name) → x ∈ defs → Elim α
  ECase : (bs : Branches α) → Elim α
  -- TODO: do we need a type annotation for the return type of case?
{-# COMPILE AGDA2HS Elim     #-}

Elims α = List (Elim α)
{-# COMPILE AGDA2HS Elims #-}

data Branch α where
  BBranch : (@0 c : name) → (c∈cons : c ∈ cons)
          → Rezz _ (lookupAll conArity c∈cons)
          → Term (lookupAll conArity c∈cons <> α) → Branch α
{-# COMPILE AGDA2HS Branch   #-}

Branches α = List (Branch α)
{-# COMPILE AGDA2HS Branches #-}

apply : {@0 α : Scope name} → Term α → Term α → Term α
apply u v = TApp u (EArg v ∷ [])

-- NOTE(flupe): agda2hs internal error
-- {-# COMPILE AGDA2HS apply #-}

elimView : {@0 α : Scope name} → Term α → Term α × Elims α
elimView (TApp u es2) = 
  case elimView u of λ where
    (u' , es1) → (u' , (es1 ++ es2))
elimView u = (u , [])
{-# COMPILE AGDA2HS elimView #-}

lookupEnv : {@0 α β : Scope name}
          → α ⇒ β
          → (@0 x : name)
          → (@(tactic auto) _ : x ∈ α)
          → Term β
lookupEnv SNil x q = emptyCase q
lookupEnv (SCons u f) x q = bindCase q (λ _ → u) (lookupEnv f x) 

{-# COMPILE AGDA2HS lookupEnv #-}

weaken         : {@0 α β   : Scope name} → α ⊆ β → Term α → Term β
weakenSort     : {@0 α β   : Scope name} → α ⊆ β → Sort α → Sort β
weakenElim     : {@0 α β   : Scope name} → α ⊆ β → Elim α → Elim β
weakenElims    : {@0 α β   : Scope name} → α ⊆ β → Elims α → Elims β
weakenBranch   : {@0 α β   : Scope name} → α ⊆ β → Branch α → Branch β
weakenBranches : {@0 α β   : Scope name} → α ⊆ β → Branches α → Branches β
weakenEnv      : {@0 α β γ : Scope name} → β ⊆ γ → Subst α β → Subst α γ

weaken p (TVar x k)    = TVar x (coerce p k)
weaken p (TDef d k)    = TDef d k
weaken p (TCon c k vs) = TCon c k (weakenEnv p vs)
weaken p (TLam x v)    = TLam x (weaken (subBindKeep p) v)
weaken p (TApp u es)   = TApp (weaken p u) (weakenElims p es)
weaken p (TPi x a b)   = TPi x (weaken p a) (weaken (subBindKeep p) b)
weaken p (TSort α)     = TSort (weakenSort p α)
weaken p (TLet x v t)  = TLet x (weaken p v) (weaken (subBindKeep p) t)
{-# COMPILE AGDA2HS weaken #-}

weakenSort p (STyp x) = STyp x
{-# COMPILE AGDA2HS weakenSort #-}

weakenElim p (EArg x)   = EArg (weaken p x)
weakenElim p (EProj x k)  = EProj x k
weakenElim p (ECase bs) = ECase (weakenBranches p bs)
{-# COMPILE AGDA2HS weakenElim #-}

weakenElims p []       = []
weakenElims p (e ∷ es) = weakenElim p e ∷ weakenElims p es
{-# COMPILE AGDA2HS weakenElims #-}

weakenBranch p (BBranch c k r x) = BBranch c k r (weaken (subJoinKeep r p) x)
{-# COMPILE AGDA2HS weakenBranch #-}

weakenBranches p []       = []
weakenBranches p (b ∷ bs) = weakenBranch p b ∷ weakenBranches p bs
{-# COMPILE AGDA2HS weakenBranches #-}

weakenEnv p SNil = SNil
weakenEnv p (SCons u e) = SCons (weaken p u) (weakenEnv p e)
{-# COMPILE AGDA2HS weakenEnv #-}

opaque
  unfolding Scope.Scope Scope.Sub

  idEnv : {@0 β : Scope name} → Rezz _ β → β ⇒ β
  idEnv (rezz [])      = SNil
  idEnv (rezz (x ∷ β)) = SCons (TVar (get x) here) (weakenEnv (subBindDrop subRefl) (idEnv (rezz β)))
  {-# COMPILE AGDA2HS idEnv #-}

  liftEnv : {@0 α β γ : Scope name} → Rezz _ α → β ⇒ γ → (α <> β) ⇒ (α <> γ)
  liftEnv (rezz []) e = e
  liftEnv (rezz (x ∷ α)) e =
    SCons (TVar (get x) here)
          (weakenEnv (subBindDrop subRefl) (liftEnv (rezz α) e))
  {-# COMPILE AGDA2HS liftEnv #-}

  liftBindEnv : {@0 α β : Scope name} {@0 x : name} → α ⇒ β → (bind x α) ⇒ (bind x β)
  liftBindEnv {x = x} e =
    SCons (TVar x here)
          (weakenEnv (subBindDrop subRefl) e)
  {-# COMPILE AGDA2HS liftBindEnv #-}

  coerceEnv : {@0 α β γ : Scope name} → Rezz _ α → α ⊆ β → β ⇒ γ → α ⇒ γ
  coerceEnv (rezz []) p e = SNil
  coerceEnv (rezz (x ∷ α)) p e =
    SCons (lookupEnv e _ (bindSubToIn p))
          (coerceEnv (rezz α) (joinSubRight (rezz [ get x ]) p) e)
  {-# COMPILE AGDA2HS coerceEnv #-}

  dropEnv : {@0 α β : Scope name} {@0 x : name} → (x ◃ α) ⇒ β → α ⇒ β
  dropEnv (SCons x f) = f
  {-# COMPILE AGDA2HS dropEnv #-}

subst : ∀ {ℓ ℓ′} {@0 a : Set ℓ} (f : @0 a → Set ℓ′) {@0 x y : a} → @0 x ≡ y → f x → f y
subst f refl x = x
{-# COMPILE AGDA2HS subst transparent #-}

opaque
  unfolding bind

  raiseEnv : {@0 α β : Scope name} → Rezz _ β → α ⇒ β → (α <> β) ⇒ β
  raiseEnv {α = α} {β} r SNil = subst (λ α → α ⇒ β) (sym ∅-<>) (idEnv r)
  raiseEnv {α = α} {β} r (SCons u e) =
    subst (λ α → α ⇒ β) (sym (<>-assoc {α = []} {β = α} {γ = β}))
                        (SCons u (raiseEnv r e))
  {-# COMPILE AGDA2HS subst raiseEnv #-}

raise : {@0 α β : Scope name} → Rezz _ α → Term β → Term (α <> β)
raise r = weaken (subRight (splitRefl r))
{-# COMPILE AGDA2HS subst raise #-}
