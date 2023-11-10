{-# OPTIONS --allow-unsolved-metas #-}

open import Scope

open import Haskell.Prelude hiding (All)

module Reduce
    {@0 name  : Set}
    (defs     : Scope name)
    (cons     : Scope name)
    (conArity : All (λ _ → Scope name) cons)
  where

open import Syntax defs cons conArity
open import Utils.Erase

private variable
  @0 α β γ : Scope name
  @0 x     : name

substTerm     : α ⇒ β → Term α → Term β
substSort     : α ⇒ β → Sort α → Sort β
substElim     : α ⇒ β → Elim α → Elim β
substElims    : α ⇒ β → Elims α → Elims β
substBranch   : α ⇒ β → Branch α → Branch β
substBranches : α ⇒ β → Branches α → Branches β
substEnv      : α ⇒ β → γ ⇒ α → γ ⇒ β

substSort f (STyp x) = STyp x
{-# COMPILE AGDA2HS substSort transparent #-}

substTerm f (TVar x k)    = lookupEnv f x k
substTerm f (TDef d k)    = TDef d k
substTerm f (TCon c k vs) = TCon c k (substEnv f vs)
substTerm f (TLam x v)    = TLam x (substTerm (liftBindEnv f) v)
substTerm f (TApp u es)   = TApp (substTerm f u) (substElims f es)
substTerm f (TPi x a b)   = TPi x (substTerm f a) (substTerm (liftBindEnv f) b)
substTerm f (TSort s)     = TSort (substSort f s)
substTerm f (TLet x u v)  = TLet x (substTerm f u) (substTerm (liftBindEnv f) v)

substElim f (EArg u)    = EArg (substTerm f u)
substElim f (EProj p k) = EProj p k
substElim f (ECase bs)  = ECase (substBranches f bs)

substElims f [] = []
substElims f (e ∷ es) = substElim f e ∷ substElims f es

substBranch f (BBranch c k aty u) = BBranch c k aty (substTerm (liftEnv aty f) u)

substBranches f [] = []
substBranches f (b ∷ bs) = substBranch f b ∷ substBranches f bs

substEnv f SNil = SNil
substEnv f (SCons x e) = SCons (substTerm f x) (substEnv f e)

substTop : Rezz _ α → Term α → Term (x ◃ α) → Term α
substTop r u = substTerm (SCons u (idEnv r))

lookupBranch : Branches α → (@0 c : name) (p : c ∈ cons) → Maybe (Term ((conArity ! c) <> α))
lookupBranch [] c k = Nothing
lookupBranch (BBranch c' k' aty u ∷ bs) c = {!!}
  -- case c ≟ c₁ of λ where
  --   (yes refl) → just v
  --   (no _)     → lookupBranch bs c

{-


opaque
  unfolding Scope.Scope

  step : {α : Scope} → Term α → Maybe (Term α)
  step (var x) = nothing
  step (def x) = nothing
  step (con c vs) = nothing
  step (lam x u) = nothing
  step (appE u []) = step u
  step (appE (lam x u) (arg v ∷ es)) = just (substTop v u)
  step (appE (con c us) (case bs ∷ es)) =
    case lookupBranch bs c of λ where
      (just v) → just (substTerm (raiseEnv us) v) 
      nothing  → nothing
  step (appE u es) = Maybe.map (λ u → appE u es) (step u)
  step (pi x a b) = nothing
  step (sort x) = nothing
  step (let′ x u v) = case step u of λ where
    (just u') → just (let′ x u' v)
    nothing   → just (substTop u v)

reduce : {α : Scope} → ℕ → Term α → Maybe (Term α)
reduce zero u = nothing
reduce (suc n) u = case (step u) of λ where
  (just u') → reduce n u'
  nothing   → just u

-- -}
