open import Haskell.Prelude hiding (All; a; b; c; s; t)

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
  @0 s s' t t' u u' v v' : Term α
  @0 k l n sa sb    : Sort α
  @0 a a' b b' c c' : Type α
  @0 w w'           : Elim α
  @0 tel            : Telescope α β
  @0 us vs          : α ⇒ β

data Conv     (@0 Γ : Context α) : @0 Term α → @0 Term α → @0 Term α → Set
data ConvElim (@0 Γ : Context α) : @0 Term α → @0 Term α → @0 Elim α → @0 Elim α → Set
data ConvSubst (@0 Γ : Context α) : @0 β ⇒ α → @0 β ⇒ α → @0 Telescope α β → Set

{-# COMPILE AGDA2HS Conv     #-}
{-# COMPILE AGDA2HS ConvElim #-}

infix 3 Conv
syntax Conv Γ t x y       = Γ ⊢ x ≅ y ∶ t
syntax ConvElim Γ t u x y = Γ ⊢ u [ x ≅ y ] ∶ t

renameTop : Rezz _ α → Term (x ◃ α) → Term (y ◃ α)
renameTop = substTerm ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTop #-}

renameTopSort : Rezz _ α → Sort (x ◃ α) → Sort (y ◃ α)
renameTopSort = substSort ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopSort #-}

renameTopType : Rezz _ α → Type (x ◃ α) → Type (y ◃ α)
renameTopType = substType ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopType #-}

data Conv {α} Γ where
  CRefl  : Γ ⊢ u ≅ u ∶ t
  CLam   : {@0 r : Rezz _ α}
         → Γ , x ∶ a ⊢ renameTop r u ≅ renameTop r v ∶ unType b
         → Γ ⊢ TLam y u ≅ TLam z v ∶ TPi x a b
  CPi    : {@0 r : Rezz _ α}
         → Γ ⊢ unType a ≅ unType a' ∶ TSort (typeSort a)
         → Γ , x ∶ a ⊢ unType b ≅ renameTop r (unType b') ∶ TSort (typeSort b)
         → Γ ⊢ TPi x a b ≅ TPi y a' b' ∶ TSort (funSort sa sb)
  CApp   : Γ ⊢ u ≅ u' ∶ s
         → Γ ⊢ u [ w ≅ w' ] ∶ t
         → Γ ⊢ TApp u w ≅ TApp u' w' ∶ t
  CRedT  : @0 ReducesTo sig t t'
         → Γ ⊢ u  ≅ v  ∶ t'
         → Γ ⊢ u  ≅ v  ∶ t
  CRedL  : @0 ReducesTo sig u u'
         → Γ ⊢ u' ≅ v  ∶ t
         → Γ ⊢ u  ≅ v  ∶ t
  CRedR  : @0 ReducesTo sig v v'
         → Γ ⊢ u  ≅ v' ∶ t
         → Γ ⊢ u  ≅ v  ∶ t

{-# COMPILE AGDA2HS Conv #-}

data ConvElim Γ where
  CERedT : @0 ReducesTo sig t t'
         → Γ ⊢ u [ w ≅ w' ] ∶ t'
         → Γ ⊢ u [ w ≅ w' ] ∶ t
  CEArg  : Γ ⊢ v ≅ v' ∶ unType a
         → Γ ⊢ u [ EArg v ≅ EArg v' ] ∶ TPi x a b
  -- TODO: CEProj : {!   !}
  -- TODO: CECase : {!   !}

{-# COMPILE AGDA2HS ConvElim #-}

data ConvSubst {α} Γ where
  CSNil : ConvSubst Γ SNil SNil EmptyTel
  CSCons : {@0 r : Rezz _ α}
         → Conv Γ u v (unType a) 
         → ConvSubst Γ us vs (substTelescope (SCons u (idSubst r)) tel)
         → ConvSubst Γ (SCons u us) (SCons v vs) (ExtendTel x a tel)

{-# COMPILE AGDA2HS ConvSubst #-}
