open import Scope

open import Haskell.Prelude hiding (All; c; t)
open import Haskell.Extra.Dec
open import Haskell.Extra.Erase

open import Utils.Either

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Syntax
open import Agda.Core.Signature

module Agda.Core.Substitute
  {{@0 globals : Globals}}
  where

private variable
  @0 x c     : Name
  @0 α β γ cs : Scope Name
  t : @0 Scope Name → Set


substTerm     : α ⇒ β → Term α → Term β
substSort     : α ⇒ β → Sort α → Sort β
substType     : α ⇒ β → Type α → Type β
substBranch   : α ⇒ β → Branch α c → Branch β c
substBranches : α ⇒ β → Branches α cs → Branches β cs
substSubst    : α ⇒ β → γ ⇒ α → γ ⇒ β
substTypeS   : α ⇒ β → γ ⇛ α → γ ⇛ β

substSort f (STyp x) = STyp x
{-# COMPILE AGDA2HS substSort #-}

substType f (El st t) = El (substSort f st) (substTerm f t)
{-# COMPILE AGDA2HS substType #-}

substTerm f (TVar (⟨ x ⟩ k))  = lookupSubst f x k
substTerm f (TDef d)          = TDef d
substTerm f (TData d ps is)   = TData d (substSubst f ps) (substSubst f is)
substTerm f (TCon c vs)       = TCon c (substSubst f vs)
substTerm f (TLam x v)        = TLam x (substTerm (liftBindSubst f) v)
substTerm f (TApp u v)        = TApp (substTerm f u) (substTerm f v)
substTerm f (TProj u p)       = TProj (substTerm f u) p
substTerm f (TCase {x = x} d r u bs m) =
  TCase {x = x} d r
    (substTerm f u)
    (substBranches f bs)
    (substType (liftBindSubst (liftSubst r f)) m)
substTerm f (TPi x a b)       = TPi x (substType f a) (substType (liftBindSubst f) b)
substTerm f (TSort s)         = TSort (substSort f s)
substTerm f (TLet x u v)      = TLet x (substTerm f u) (substTerm (liftBindSubst f) v)
substTerm f (TAnn u t)        = TAnn (substTerm f u) (substType f t)
{-# COMPILE AGDA2HS substTerm #-}

substBranch f (BBranch c r u) = BBranch c r (substTerm (liftSubst r f) u)
{-# COMPILE AGDA2HS substBranch #-}

substBranches f BsNil = BsNil
substBranches f (BsCons b bs) = BsCons (substBranch f b) (substBranches f bs)
{-# COMPILE AGDA2HS substBranches #-}

substSubst f SNil = SNil
substSubst f (SCons x e) = SCons (substTerm f x) (substSubst f e)
{-# COMPILE AGDA2HS substSubst #-}

substTypeS f ⌈⌉ = ⌈⌉
substTypeS f ⌈ e ◃ _ ∶ x ⌉ = YCons (substType f x) (substTypeS f e)
{-# COMPILE AGDA2HS substTypeS #-}

record Substitute (t : @0 Scope Name → Set) : Set where
  field subst : (α ⇒ β) → t α → t β
open Substitute {{...}} public
{-# COMPILE AGDA2HS Substitute class #-}

instance
  iSubstTerm : Substitute Term
  iSubstTerm .subst = substTerm
  iSubstType : Substitute Type
  iSubstType .subst = substType
  iSubstSort : Substitute Sort
  iSubstSort .subst = substSort
  iSubstBranch : Substitute (λ α → Branch α c)
  iSubstBranch .subst = substBranch
  iSubstBranches : Substitute (λ α → Branches α cs)
  iSubstBranches .subst = substBranches
  iSubstSubst : Substitute (Subst α)
  iSubstSubst .subst = substSubst
  iSubstTypeS : Substitute (TypeS α)
  iSubstTypeS .subst = substTypeS
{-# COMPILE AGDA2HS iSubstTerm #-}
{-# COMPILE AGDA2HS iSubstType #-}
{-# COMPILE AGDA2HS iSubstSort #-}
{-# COMPILE AGDA2HS iSubstBranch #-}
{-# COMPILE AGDA2HS iSubstBranches #-}
{-# COMPILE AGDA2HS iSubstSubst #-}
{-# COMPILE AGDA2HS iSubstTypeS #-}

substTop : {{Substitute t}} → Rezz α → Term α → t (x ◃ α) → t α
substTop r u = subst (SCons u (idSubst r))
{-# COMPILE AGDA2HS substTop #-}

substTelescope : (α ⇒ β) → Telescope α γ → Telescope β γ
substTelescope f EmptyTel = EmptyTel
substTelescope f (ExtendTel x a tel) = ExtendTel x (substType f a) (substTelescope (liftBindSubst f) tel)
{-# COMPILE AGDA2HS substTelescope #-}

instance
  iSubstTelescope : Substitute (λ α → Telescope α β)
  iSubstTelescope .subst = substTelescope
{-# COMPILE AGDA2HS iSubstTelescope #-}
