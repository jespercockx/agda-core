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
  @0 x y z          : name
  @0 α β γ          : Scope name
  @0 s s' t t' u u' v v' : Term α
  @0 k l n sa sb    : Sort α
  @0 a a' b b' c c' : Type α
  @0 w w'           : Elim α
  @0 tel            : Telescope α β
  @0 us vs          : α ⇒ β

data Conv     (@0 Γ : Context α) : @0 Term α → @0 Term α → @0 Term α → Set
data ConvElim (@0 Γ : Context α) : @0 Term α → @0 Term α → @0 Elim α → @0 Elim α → @0 ((Elim α → Term α) → Term α) → Set
data ConvSubst (@0 Γ : Context α) : @0 β ⇒ α → @0 β ⇒ α → @0 Telescope α β → Set

{-# COMPILE AGDA2HS Conv     #-}
{-# COMPILE AGDA2HS ConvElim #-}
{-# COMPILE AGDA2HS ConvSubst #-}

infix 3 Conv
syntax Conv Γ t x y          = Γ ⊢ x ≅ y ∶ t
syntax ConvElim Γ t u x y f  = Γ [ u ∶ t ] ⊢ x ≅ y ∶ f
syntax ConvSubst Γ us vs tel = Γ ⊢ [ us ≅ vs ] ⇒ tel

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
         → Γ ⊢ TPi x a b ≅ TPi y a' b' ∶ TSort k
  CApp   : {@0 f : (Elim α → Term α) → Term α}
         → Γ ⊢ u ≅ u' ∶ s
         → Γ [ u ∶ s ] ⊢ w ≅ w' ∶ f
         → Γ ⊢ TApp u w ≅ TApp u' w' ∶ f (TApp u)
  CCon   : {@0 d : name} (@0 dp : d ∈ defScope) (@0 dt : Datatype)
         → {@0 c : name} (@0 cq : c ∈ dataConstructorScope dt)
         → @0 getDefinition sig d dp ≡ DatatypeDef dt
         → (let (cp Σ, con) = lookupAll (dataConstructors dt) cq)
         → {@0 pars : dataParameterScope dt ⇒ α}
         → {@0 ixs  : dataIndexScope dt ⇒ α}
         → {@0 us vs : lookupAll fieldScope cp ⇒ α}
         → ConvSubst Γ us vs (substTelescope pars (conTelescope con))
         → Γ ⊢ TCon c cp us ≅ TCon c cp vs ∶ unType (dataType d dp (substSort pars (dataSort dt)) pars ixs)
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

data ConvElim {α} Γ where
  CERedT : {@0 f : (Elim α → Term α) → Term α}
           (@0 _ : ReducesTo sig t t')
         → Γ [ u ∶ t' ] ⊢ w ≅ w' ∶ f
         → Γ [ u ∶ t  ] ⊢ w ≅ w' ∶ f
  CEArg  : {@0 r : Rezz _ α}
         → Γ ⊢ s ≅ TPi x a b ∶ TSort k
         → Γ ⊢ v ≅ v' ∶ unType a
         → Γ [ u ∶ s ] ⊢ EArg v ≅ EArg v' ∶ (λ _ → substTop r v (unType b))
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
