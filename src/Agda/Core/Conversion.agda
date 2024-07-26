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
  @0 x y z c cn     : name
  @0 α β γ cs       : Scope name
  @0 s s' t t' u u' v v' : Term α
  @0 k l n sa sb    : Sort α
  @0 a a' b b'      : Type α
  @0 w w'           : Elim α
  @0 tel            : Telescope α β
  @0 us vs          : α ⇒ β
  @0 r              : Rezz _ α


data Conv     {@0 α} : @0 Term α → @0 Term α → Set
data ConvElim {@0 α} : @0 Elim α → @0 Elim α → Set
data ConvBranch {@0 α} : (@0 b₁ b₂ : Branch α cn) → Set
data ConvBranches {@0 α} : (@0 bs₁ bs₂ : Branches α cs) → Set
data ConvSubst {@0 α} : (@0 us₁ us₂ : β ⇒ α) → Set
infix 3 Conv
syntax Conv x y        = x ≅ y
syntax ConvElim x y    = x ≃ y
syntax ConvSubst us vs = us ⇔ vs

{-# COMPILE AGDA2HS Conv     #-}
{-# COMPILE AGDA2HS ConvElim #-}
{-# COMPILE AGDA2HS ConvBranch #-}
{-# COMPILE AGDA2HS ConvBranches #-}
{-# COMPILE AGDA2HS ConvSubst #-}

renameTop : Rezz _ α → Term (x ◃ α) → Term (y ◃ α)
renameTop = substTerm ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTop #-}

renameTopSort : Rezz _ α → Sort (x ◃ α) → Sort (y ◃ α)
renameTopSort = substSort ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopSort #-}

renameTopType : Rezz _ α → Type (x ◃ α) → Type (y ◃ α)
renameTopType = substType ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopType #-}
data Conv {α} where
  CCon   : (@0 cp : c ∈ conScope) {@0 us vs : fieldsOf cp ⇒ α}
         → ConvSubst us vs → TCon c cp us ≅ TCon c cp vs
  CRefl  : u ≅ u
  CLam   : renameTop {y = x} r u ≅ renameTop {y = x} r v
         → TLam y u ≅ TLam z v
  CPi    : unType a ≅ unType a'
         → unType b ≅ renameTop r (unType b')
         → TPi x a b ≅ TPi y a' b'
  CApp   : u ≅ u'
         → w ≃ w'
         → TApp u w ≅ TApp u' w'
  CRedL  : @0 ReducesTo sig u u'
         → u' ≅ v
         → u  ≅ v
  CRedR  : @0 ReducesTo sig v v'
         → u  ≅ v'
         → u  ≅ v

data ConvSubst {α} where
  CSNil : ConvSubst {β = ∅} us vs
  CSCons : {@0 x : name} → u ≅ v → us ⇔ vs
         → (SCons {x = x} u us) ⇔ (SCons {x = x} v vs)

data ConvElim {α} where
  CEArg  : v ≅ v' → EArg v ≃ EArg v'

  CECase : (bs bp : Branches α cs)
           (ms : Type (x ◃ α)) (mp : Type (y ◃ α))
         → renameTop {y = z} r (unType ms) ≅ renameTop r (unType mp)
         → ConvBranches bs bp → ECase bs ms ≃ ECase bp mp

data ConvBranches {α} where
  CBranchesNil : {bs bp : Branches α ∅} → ConvBranches bs bp
  CBranchesCons : {b1 b2 : Branch α cn} {bs1 bs2 : Branches α cs}
                → ConvBranch b1 b2
                → ConvBranches bs1 bs2
                → ConvBranches (BsCons b1 bs1) (BsCons b2 bs2)

data ConvBranch {α} where
  CBBranch : (@0 c : name) (cp : c ∈ conScope) (r1 r2 : _)
             (t1 t2 : Term (~ fieldsOf cp <> α))
           → t1 ≅ t2
           → ConvBranch (BBranch c cp r1 t1) (BBranch c cp r2 t2)
