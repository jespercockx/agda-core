open import Scope.Core
open import Scope.Split
open import Scope.Sub
open import Scope.In
open import Scope.All

open import Haskell.Extra.Dec
open import Utils.Either
open import Haskell.Extra.Erase
open import Haskell.Extra.Delay

open import Haskell.Prelude hiding (All; a; b; c; t)

import Syntax

module Conversion
  {@0 name  : Set}
  (@0 defs     : Scope name)
  (@0 cons     : Scope name)
  (@0 conArity : All (λ _ → Scope name) cons)
  (@0 defType  : All (λ _ → Syntax.Type defs cons conArity mempty) defs)
  where

open Syntax defs cons conArity
open import Substitute defs cons conArity
open import Reduce defs cons conArity
open import Context defs cons conArity

private variable
  @0 x y z : name
  @0 α β γ : Scope name
  @0 t t' u u' v v' : Term α
  @0 k l n : Sort α
  @0 a a' b b' c c' : Type α
  @0 w w' : Elim α

data Conv (@0 Γ : Context α) : @0 Type α → @0 Term α → @0 Term α → Set
data ConvElim (@0 Γ : Context α) : @0 Type α → @0 Term α → @0 Elim α → @0 Elim α → Set

@0 renameTop : Term (x ◃ α) → Term (y ◃ α)
renameTop {x = x} {y = y} = substTerm (liftBindSubst {x = x} {y = y} (idSubst (rezz _)))

data Conv {α} Γ where
  CRefl  : Conv Γ t u u
  CLam   : Conv {α = x ◃ α} (Γ , x ∶ a) b (renameTop u) (renameTop v)
         → Conv Γ (TPi x k l a b) (TLam y u) (TLam z v)
  CPi    : Conv Γ (TSort k) a a'
         → Conv (Γ , x ∶ a) (TSort (weakenSort (subWeaken subRefl) l)) b (renameTop b')
         → Conv Γ (TSort (funSort k l)) (TPi x k l a b) (TPi y k l a' b')
  CApp   : Conv Γ a u u'
         → ConvElim Γ a u w w'
         -- Note: We assume all terms are well-typed, so we allow any type b here
         → Conv Γ b (TApp u w) (TApp u' w')
  CRedT  : @0 HasResult t' (reduce (rezz _) t)
         → Conv Γ t' u v → Conv Γ t u v
  CRedL  : @0 HasResult u' (reduce (rezz _) u)
         → Conv Γ t u' v → Conv Γ t u v
  CRedR  : @0 HasResult v' (reduce (rezz _) v)
         → Conv Γ t u v' → Conv Γ t u v

{-# COMPILE AGDA2HS Conv #-}

data ConvElim Γ where
  CERedT : @0 HasResult t' (reduce (rezz _) t)
         → ConvElim Γ t' u w w' → ConvElim Γ t u w w'
  CEArg  : Conv Γ a v v'
         → ConvElim Γ (TPi x k l a b) u (EArg v) (EArg v')
  -- TODO: CEProj : {!   !}
  -- TODO: CECase : {!   !}

{-# COMPILE AGDA2HS ConvElim #-}
