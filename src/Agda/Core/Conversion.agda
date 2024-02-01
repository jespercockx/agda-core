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

private open module @0 G = Globals globals

open import Haskell.Extra.Dec
open import Utils.Either
open import Haskell.Extra.Erase

open import Agda.Core.Syntax globals
open import Agda.Core.Substitute globals
open import Agda.Core.Reduce globals
open import Agda.Core.Context globals
open import Agda.Core.Utils renaming (_,_ to _Σ,_)

private variable
  @0 x y z cn       : name
  @0 α β γ cs       : Scope name
  @0 s s' t t' u u' v v' : Term α
  @0 k l n sa sb    : Sort α
  @0 a a' b b' c c' : Type α
  @0 w w'           : Elim α
  @0 tel            : Telescope α β
  @0 us vs          : α ⇒ β

data Conv     (@0 Γ : Context α) : @0 Term α → @0 Term α → Set
data ConvElim (@0 Γ : Context α) : @0 Elim α → @0 Elim α → Set
data ConvBranch (@0 Γ : Context α) : @0 Branch α cn → @0 Branch α cn → Set
data ConvSubst (@0 Γ : Context α) : @0 β ⇒ α → @0 β ⇒ α → Set

data ConvBranches (@0 Γ : Context α) : @0 Branches α cs → @0 Branches α cs → Set where
  CBranchesNil : ConvBranches Γ BsNil BsNil
  CBranchesCons : {b1 b2 : Branch α cn} {bs1 bs2 : Branches α cs} → ConvBranch Γ b1 b2 → ConvBranches Γ bs1 bs2 → ConvBranches Γ (BsCons b1 bs1) (BsCons b2 bs2)


{-# COMPILE AGDA2HS Conv     #-}
{-# COMPILE AGDA2HS ConvElim #-}
{-# COMPILE AGDA2HS ConvBranch #-}
{-# COMPILE AGDA2HS ConvBranches #-}
{-# COMPILE AGDA2HS ConvSubst #-}

infix 3 Conv
syntax Conv Γ x y        = Γ ⊢ x ≅ y
syntax ConvElim Γ x y    = Γ ⊢ x ≃ y
syntax ConvSubst Γ us vs = Γ ⊢ us ⇔ vs

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
  CRefl  : Γ ⊢ u ≅ u
  CLam   : {@0 r : Rezz _ α}
         --TODO: enforce that a is the type of y and z
         → Γ , x ∶ a ⊢ renameTop r u ≅ renameTop r v
         → Γ ⊢ TLam y u ≅ TLam z v
  CPi    : {@0 r : Rezz _ α}
         → Γ ⊢ unType a ≅ unType a'
         → Γ , x ∶ a ⊢ unType b ≅ renameTop r (unType b')
         → Γ ⊢ TPi x a b ≅ TPi y a' b' 
  CApp   : Γ ⊢ u ≅ u'
         → Γ ⊢ w ≃ w'
         → Γ ⊢ TApp u w ≅ TApp u' w'
  CCon   : {@0 c : name} (@0 cp : c ∈ conScope)
           {@0 us vs : lookupAll fieldScope cp ⇒ α}
         → Γ ⊢ us ⇔ vs
         → Γ ⊢ TCon c cp us ≅ TCon c cp vs
  CRedL  : @0 ReducesTo sig u u'
         → Γ ⊢ u' ≅ v
         → Γ ⊢ u  ≅ v
  CRedR  : @0 ReducesTo sig v v'
         → Γ ⊢ u  ≅ v'
         → Γ ⊢ u  ≅ v 

{-# COMPILE AGDA2HS Conv #-}

data ConvElim {α} Γ where
  CEArg  : Γ ⊢ v ≅ v'
         → Γ ⊢ EArg v ≃ EArg v'
  CECase : (bs bp : Branches α cs)
         → ConvBranches Γ bs bp
         → Γ ⊢ ECase bs ≃ ECase bp
  -- TODO: CEProj : {!   !}

data ConvBranch {α} Γ where
  CBBranch : (@0 c : name) (cp : c ∈ conScope) (r1 r2 : _)
             --TODO enforce that tel is the telescope of constructor c applied to params
             (tel : Telescope α (lookupAll fieldScope cp))
             (t1 t2 : Term (revScope (lookupAll fieldScope cp) <> α))
           → (addContextTel tel Γ) ⊢ t1 ≅ t2
           → ConvBranch Γ (BBranch c cp r1 t1) (BBranch c cp r2 t2)

{-# COMPILE AGDA2HS ConvElim #-}

data ConvSubst {α} Γ where
  CSNil : ConvSubst Γ {β = mempty} us vs
  CSCons : {@0 x : name} 
         → Conv Γ u v
         → ConvSubst Γ us vs
         → ConvSubst Γ (SCons {x = x} u us) (SCons {x = x} v vs)

{-# COMPILE AGDA2HS ConvSubst #-}
