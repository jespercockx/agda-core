open import Haskell.Prelude hiding (All; a; b; c; t)

open import Scope
open import Agda.Core.GlobalScope using (Globals)

import Agda.Core.Signature as Signature

module Agda.Core.Conversion
  {@0 name    : Set}
  (@0 globals : Globals name)
  (open Signature globals)
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
  @0 x y z          : name
  @0 α β γ          : Scope name
  @0 t t' u u' v v' : Term α
  @0 k l n sa sb    : Sort α
  @0 a a' b b' c c' : Type α
  @0 w w'           : Elim α

data Conv     (@0 Γ : Context α) : @0 Type α → @0 Term α → @0 Term α → Set
data ConvElim (@0 Γ : Context α) : @0 Type α → @0 Term α → @0 Elim α → @0 Elim α → Set

{-# COMPILE AGDA2HS Conv     #-}
{-# COMPILE AGDA2HS ConvElim #-}

infix 3 Conv
syntax Conv Γ t x y       = Γ ⊢ x ≅ y ∶ t
syntax ConvElim Γ t u x y = Γ ⊢ u [ x ≅ y ] ∶ t

renameTop : Rezz _ α → Term (x ◃ α) → Term (y ◃ α)
renameTop = substTerm ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTop #-}

@0 renameTopE : Term (x ◃ α) → Term (y ◃ α)
renameTopE = renameTop (rezz _)

data Conv {α} Γ where
  CRefl  : Γ ⊢ u ≅ u ∶ t
  CLam   : Γ , x ∶ a ⊢ renameTopE u ≅ renameTopE v ∶ b
         → Γ ⊢ TLam y u ≅ TLam z v ∶ TPi x k l a b
  CPi    : Γ ⊢ a ≅ a' ∶ TSort sa
         → Γ , x ∶ a ⊢ b ≅ renameTopE b' ∶ TSort (weakenSort (subWeaken subRefl) sb)
         → Γ ⊢ TPi x sa sb a b ≅ TPi y sa sb a' b' ∶ TSort (funSort sa sb)
  CApp   : Γ ⊢ u ≅ u' ∶ a
         → Γ ⊢ u [ w ≅ w' ] ∶ a
         → Γ ⊢ TApp u w ≅ TApp u' w' ∶ b
  CRedT  : @0 ReducesTo sig t t'
         → Γ ⊢ u  ≅ v  ∶ t'
         → Γ ⊢ u  ≅ v  ∶ t
  CRedL  : @0 ReducesTo sig u u'
         → Γ ⊢ u' ≅ v  ∶ t
         → Γ ⊢ u  ≅ v  ∶ t
  CRedR  : @0 ReducesTo sig u v'
         → Γ ⊢ u  ≅ v' ∶ t
         → Γ ⊢ u  ≅ v  ∶ t

{-# COMPILE AGDA2HS Conv #-}

data ConvElim Γ where
  CERedT : @0 ReducesTo sig t t'
         → Γ ⊢ u [ w ≅ w' ] ∶ t'
         → Γ ⊢ u [ w ≅ w' ] ∶ t
  CEArg  : Γ ⊢ v ≅ v' ∶ a
         → Γ ⊢ u [ EArg v ≅ EArg v' ] ∶ TPi x sa sb a b
  -- TODO: CEProj : {!   !}
  -- TODO: CECase : {!   !}

{-# COMPILE AGDA2HS ConvElim #-}
