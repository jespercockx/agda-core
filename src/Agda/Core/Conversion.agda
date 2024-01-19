open import Haskell.Prelude hiding (All; a; b; c; t)

open import Scope
open import Agda.Core.GlobalScope using (Globals)

import Agda.Core.Signature

module Agda.Core.Conversion
  {@0 name    : Set}
  (@0 globals : Globals name)
  (open Agda.Core.Signature globals)
  (@0 sig     : Signature)
  where

open import Haskell.Extra.Dec
open import Utils.Either
open import Haskell.Extra.Erase

open import Agda.Core.Syntax globals
open import Agda.Core.Substitute globals
open import Agda.Core.Reduce globals
open import Agda.Core.Context globals

private variable
  @0 x y z : name
  @0 α β γ : Scope name
  @0 t t' u u' v v' : Term α
  @0 k l n : Sort α
  @0 a a' b b' c c' : Type α
  @0 w w' : Elim α

data Conv (@0 Γ : Context α) : @0 Type α → @0 Term α → @0 Term α → Set
data ConvElim (@0 Γ : Context α) : @0 Type α → @0 Term α → @0 Elim α → @0 Elim α → Set

renameTop : Rezz _ α → Term (x ◃ α) → Term (y ◃ α)
renameTop {x = x} {y = y} r = substTerm (liftBindSubst {x = x} {y = y} (idSubst r))

@0 renameTopE : Term (x ◃ α) → Term (y ◃ α)
renameTopE = renameTop (rezz _)

data Conv {α} Γ where
  CRefl  : Conv Γ t u u
  CLam   : Conv {α = x ◃ α} (Γ , x ∶ a) b (renameTopE u) (renameTopE v)
         → Conv Γ (TPi x k l a b) (TLam y u) (TLam z v)
  CPi    : Conv Γ (TSort k) a a'
         → Conv (Γ , x ∶ a) (TSort (weakenSort (subWeaken subRefl) l)) b (renameTopE b')
         → Conv Γ (TSort (funSort k l)) (TPi x k l a b) (TPi y k l a' b')
  CApp   : Conv Γ a u u'
         → ConvElim Γ a u w w'
         -- Note: We assume all terms are well-typed, so we allow any type b here
         → Conv Γ b (TApp u w) (TApp u' w')
  CRedT  : @0 ReducesTo sig t t'
         → Conv Γ t' u v → Conv Γ t u v
  CRedL  : @0 ReducesTo sig u u'
         → Conv Γ t u' v → Conv Γ t u v
  CRedR  : @0 ReducesTo sig v v'
         → Conv Γ t u v' → Conv Γ t u v

{-# COMPILE AGDA2HS Conv #-}

data ConvElim Γ where
  CERedT : @0 ReducesTo sig t t'
         → ConvElim Γ t' u w w' → ConvElim Γ t u w w'
  CEArg  : Conv Γ a v v'
         → ConvElim Γ (TPi x k l a b) u (EArg v) (EArg v')
  -- TODO: CEProj : {!   !}
  -- TODO: CECase : {!   !}

{-# COMPILE AGDA2HS ConvElim #-}
