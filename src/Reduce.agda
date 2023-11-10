{-# OPTIONS --allow-unsolved-metas #-}

open import Scope.Core
open import Scope.In
open import Scope.All

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
  @0 x     : name
  @0 α β γ : Scope name

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
{-# COMPILE AGDA2HS substTerm #-}

substElim f (EArg u)    = EArg (substTerm f u)
substElim f (EProj p k) = EProj p k
substElim f (ECase bs)  = ECase (substBranches f bs)
{-# COMPILE AGDA2HS substTerm #-}

substElims f [] = []
substElims f (e ∷ es) = substElim f e ∷ substElims f es
{-# COMPILE AGDA2HS substElims #-}

substBranch f (BBranch c k aty u) = BBranch c k aty (substTerm (liftEnv aty f) u)
{-# COMPILE AGDA2HS substBranch #-}

substBranches f [] = []
substBranches f (b ∷ bs) = substBranch f b ∷ substBranches f bs
{-# COMPILE AGDA2HS substBranches #-}

substEnv f SNil = SNil
substEnv f (SCons x e) = SCons (substTerm f x) (substEnv f e)
{-# COMPILE AGDA2HS substEnv #-}

substTop : Rezz _ α → Term α → Term (x ◃ α) → Term α
substTop r u = substTerm (SCons u (idEnv r))
{-# COMPILE AGDA2HS substTop #-}

lookupBranch : Branches α → (@0 c : name) (p : c ∈ cons) → Maybe (Term ((lookupAll conArity p) <> α))
lookupBranch [] c k = Nothing
lookupBranch (BBranch c' k' aty u ∷ bs) c = {!!}
{-# COMPILE AGDA2HS lookupBranch #-}
  -- case c ≟ c₁ of λ where
  --   (yes refl) → just v
  --   (no _)     → lookupBranch bs c

opaque
  unfolding Scope

  -- NOTE(flupe): agda2hs won't allow α now, but it should be turned explicit when compiled
  step : {α : Scope name} → Term α → Maybe (Term α)
  step (TVar x _) = Nothing
  step (TDef x _) = Nothing
  step (TCon c _ vs) = Nothing
  step (TLam x u) = Nothing
  step (TApp u []) = step u
  step (TApp (TLam x u) (EArg v ∷ es)) = Just (substTop (rezz _) v u)
  step (TApp (TCon c k us) (ECase bs ∷ es)) =
    case lookupBranch bs c k of λ where
      (Just v) → Just (substTerm (raiseEnv (rezz _) us) v) 
      Nothing  → Nothing
  step (TApp u es) = fmap (λ u → TApp u es) (step u)
  step (TPi x a b) = Nothing
  step (TSort x) = Nothing
  step (TLet x u v) = case step u of λ where
    (Just u') → Just (TLet x u' v)
    Nothing   → Just (substTop (rezz _) u v)
  {-# COMPILE AGDA2HS step #-}

reduce : {α : Scope name} (fuel : Nat) → Term α → Maybe (Term α)
reduce zero u = Nothing
reduce (suc n) u = case (step u) of λ where
  (Just u') → reduce n u'
  Nothing   → Just u
{-# COMPILE AGDA2HS reduce #-}
