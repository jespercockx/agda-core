
open import Scope.Core
open import Scope.Split
open import Scope.Sub
open import Scope.In
open import Scope.All

open import Haskell.Extra.Dec
open import Utils.Either

open import Haskell.Prelude hiding (All)

module Substitute
  {@0 name  : Set}
  (@0 defs     : Scope name)
  (@0 cons     : Scope name)
  (@0 conArity : All (λ _ → Scope name) cons)
  where

open import Syntax defs cons conArity
open import Haskell.Extra.Erase

private variable
  @0 x     : name
  @0 α β γ : Scope name

substTerm     : α ⇒ β → Term α → Term β
substSort     : α ⇒ β → Sort α → Sort β
substElim     : α ⇒ β → Elim α → Elim β
substElims    : α ⇒ β → Elims α → Elims β
substBranch   : α ⇒ β → Branch α → Branch β
substBranches : α ⇒ β → Branches α → Branches β
substSubst    : α ⇒ β → γ ⇒ α → γ ⇒ β

substSort f (STyp x) = STyp x
{-# COMPILE AGDA2HS substSort #-}

substTerm f (TVar x k)        = lookupSubst f x k
substTerm f (TDef d k)        = TDef d k
substTerm f (TCon c k vs)     = TCon c k (substSubst f vs)
substTerm f (TLam x v)        = TLam x (substTerm (liftBindSubst f) v)
substTerm f (TApp u v)        = TApp (substTerm f u) (substElim f v)
substTerm f (TPi x sa sb a b) =
  TPi x (substSort f sa) (substSort f sb) (substTerm f a) (substTerm (liftBindSubst f) b)
substTerm f (TSort s)         = TSort (substSort f s)
substTerm f (TLet x u v)      = TLet x (substTerm f u) (substTerm (liftBindSubst f) v)
{-# COMPILE AGDA2HS substTerm #-}

substElim f (EArg u)    = EArg (substTerm f u)
substElim f (EProj p k) = EProj p k
substElim f (ECase bs)  = ECase (substBranches f bs)
{-# COMPILE AGDA2HS substElim #-}

substElims f = map (substElim f)
{-# COMPILE AGDA2HS substElims #-}

substBranch f (BBranch c k aty u) = BBranch c k aty (substTerm (liftSubst aty f) u)
{-# COMPILE AGDA2HS substBranch #-}

substBranches f [] = []
substBranches f (b ∷ bs) = substBranch f b ∷ substBranches f bs
{-# COMPILE AGDA2HS substBranches #-}

substSubst f SNil = SNil
substSubst f (SCons x e) = SCons (substTerm f x) (substSubst f e)
{-# COMPILE AGDA2HS substSubst #-}

substTop : Rezz _ α → Term α → Term (x ◃ α) → Term α
substTop r u = substTerm (SCons u (idSubst r))
{-# COMPILE AGDA2HS substTop #-}
