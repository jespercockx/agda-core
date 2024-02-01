open import Scope
import Utils.List as List

open import Agda.Core.GlobalScope using (Globals)
import Agda.Core.Signature as Signature

open import Haskell.Prelude hiding (All; a; b; c; e; s; t; m)

module Agda.Core.Typing
    {@0 name    : Set}
    (@0 globals : Globals name)
    (open Signature globals)
    (@0 sig     : Signature)
  where

private open module @0 G = Globals globals

open import Haskell.Extra.Erase
open import Haskell.Extra.Loop
open import Haskell.Law.Monoid
open import Haskell.Law.Equality

open import Utils.Tactics using (auto)

open import Agda.Core.Syntax globals
open import Agda.Core.Reduce globals
open import Agda.Core.Conversion globals sig
open import Agda.Core.Context globals
open import Agda.Core.Substitute globals
open import Agda.Core.Utils renaming (_,_ to _Σ,_)

private variable
  @0 x y     : name
  @0 α β pars ixs : Scope name
  @0 s t u v : Term α
  @0 a b c   : Type α
  @0 k l m   : Sort α
  @0 n       : Nat
  @0 e       : Elim α
  @0 tel     : Telescope α β
  @0 us vs   : α ⇒ β

constructorType : (@0 d : name) (dp : d ∈ defScope)
                → (@0 c : name) (cp : c ∈ conScope)
                → (con : Constructor pars ixs c cp)
                → Sort α
                → pars ⇒ α
                → lookupAll fieldScope cp ⇒ α
                → Type α
constructorType d dp c cp con ds pars us = 
  dataType d dp ds pars (substSubst (concatSubst us pars) (conIndices con))
{-# COMPILE AGDA2HS constructorType #-}


addContextTel : Telescope α β → Context α → Context (β <> α)
addContextTel EmptyTel c = subst' Context (sym (leftIdentity _)) c
addContextTel (ExtendTel x ty telt) c =
  subst' Context
    (associativity _ [ x ] _)
    (addContextTel telt (c , x ∶ ty))
{-# COMPILE AGDA2HS addContextTel #-}

data TyTerm (@0 Γ : Context α) : @0 Term α → @0 Type α → Set

-- TyElim Γ e t f means: if  Γ ⊢ u : t  then  Γ ⊢ appE u [ e ] : f (appE u)
data TyElim  (@0 Γ : Context α) : @0 Elim α → @0 Type α → @0 Type (x ◃ α) → Set

data TySubst (@0 Γ : Context α) : (β ⇒ α) → @0 Telescope α β → Set

data TyBranch (@0 Γ : Context α) (@0 dt : Datatype)
              (@0 ps : dataParameterScope dt ⇒ α)
              (@0 rt : Type (x ◃ α)) : @0 Branch α → Set

infix 3 TyTerm
syntax TyTerm Γ u t = Γ ⊢ u ∶ t

data TyTerm {α} Γ where

  TyTVar
    : (@0 p : x ∈ α)
    ----------------------------------
    → Γ ⊢ TVar x p ∶ lookupVar Γ x p

  TyDef
    : {@0 f : name} (@0 p : f ∈ defScope)
    ----------------------------------------------
    → Γ ⊢ TDef f p ∶ weakenType subEmpty (getType sig f p)

  TyCon
    : {@0 d : name} (@0 dp : d ∈ defScope) (@0 dt : Datatype)
    → {@0 c : name} (@0 cq : c ∈ dataConstructorScope dt)
    → @0 getDefinition sig d dp ≡ DatatypeDef dt
    → (let (cp Σ, con) = lookupAll (dataConstructors dt) cq)
    → {@0 pars : dataParameterScope dt ⇒ α}
    → {@0 us : lookupAll fieldScope cp ⇒ α}
    → TySubst Γ us (substTelescope pars (conTelescope con))
    -----------------------------------------------------------
    → Γ ⊢ TCon c cp us ∶ constructorType d dp c cp con (substSort pars (dataSort dt)) pars us

  TyLam
    : {@0 r : Rezz _ α}
    → Γ , x ∶ a ⊢ u ∶ renameTopType r b
    -------------------------------
    → Γ ⊢ TLam x u ∶ El k (TPi y a b)

  TyAppE
    : {@0 r : Rezz _ α}
      {b : Type (x ◃ α)}
    → Γ ⊢ u ∶ a
    → TyElim Γ e a b
    ------------------------------------
    → Γ ⊢ TApp u e ∶ (substTopType r u b)

  TyPi
    : Γ ⊢ u ∶ sortType k
    → Γ , x ∶ (El k u) ⊢ v ∶ sortType l
    ----------------------------------------------------------
    → Γ ⊢ TPi x (El k u) (El l v) ∶ sortType (piSort k l)

  TyType
    -------------------------------------------
    : Γ ⊢ TSort k ∶ sortType (sucSort k)

  TyLet
    : {@0 r : Rezz _ α}
    → Γ ⊢ u ∶ a
    → Γ , x ∶ a ⊢ v ∶ weakenType (subWeaken subRefl) b
    ----------------------------------------------
    → Γ ⊢ TLet x u v ∶ b

  TyAnn
    : Γ ⊢ u ∶ a
    ------------------
    → Γ ⊢ TAnn u a ∶ sortType (typeSort a)

  TyConv
    : Γ ⊢ u ∶ a
    → Γ ⊢ (unType a) ≅ (unType b) ∶ (unType c)
    ----------------
    → Γ ⊢ u ∶ b

{-# COMPILE AGDA2HS TyTerm #-}

data TyElim {α} Γ where
    TyArg : {@0 r : Rezz _ α}
            {@0 w : name}
          → Γ ⊢ (unType c) ≅ TPi x a b ∶ TSort k
          → Γ ⊢ u ∶ a
          → TyElim Γ (EArg u) c (weakenType {β = w ◃ α} (subBindDrop subRefl) (substTopType r u b))
    TyCase : {@0 d : name} (@0 dp : d ∈ defScope) (@0 dt : Datatype)
             (@0 de : getDefinition sig d dp ≡ DatatypeDef dt)
             {@0 ps : dataParameterScope dt ⇒ α}
             {@0 is : dataIndexScope dt ⇒ α}
             (bs : Branches α)
             (rt : Type (x ◃ α))
           → Γ ⊢ (unType c) ≅ (unType $ dataType d dp k ps is) ∶ (TSort k)
           → List.All (λ b → TyBranch Γ dt ps rt b) bs
           → TyElim Γ (ECase bs) c rt
    -- TODO: proj
    -- TODO: case

{-# COMPILE AGDA2HS TyElim #-}

data TyBranch {α} Γ dt ps rt where
  TyBBranch : (@0 c : name) → (c∈dcons : c ∈ dataConstructorScope dt)
            → (let (c∈cons Σ, con ) = lookupAll (dataConstructors dt) c∈dcons)
            → {@0 r : Rezz _ (lookupAll fieldScope c∈cons)}
              {@0 rα : Rezz _ α}
              (rhs : Term (lookupAll fieldScope c∈cons <> α))
              (let ctel = substTelescope ps (conTelescope con)
                   cargs = weakenSubst (subLeft (splitRefl r)) (idSubst r)
                   idsubst = (weakenSubst (subJoinDrop r subRefl) (idSubst (rα)))
                   bsubst = (SCons (TCon c c∈cons cargs) idsubst))
            → TyTerm (addContextTel ctel Γ) rhs (substType bsubst rt)
            → TyBranch Γ dt ps rt (BBranch c c∈cons r rhs)

data TySubst {α} Γ where
  TyNil  : TySubst Γ SNil EmptyTel
  TyCons : {@0 r : Rezz _ α}
         → TyTerm Γ u a
         → TySubst Γ us (substTelescope (SCons u (idSubst r)) tel)
         → TySubst Γ (SCons u us) (ExtendTel x a tel)

{-# COMPILE AGDA2HS TySubst #-}

{-
-- TyElims Γ es f t₁ t₂ means: if  Γ ⊢ h [] : t₁  then  Γ ⊢ h es : t₂
data TyElims Γ where
    TyDone : ∀ {@0 u} → TyElims Γ [] u t t
    TyMore : ∀ {@0 h f}
        → TyElim  Γ e        s             f
        → TyElims Γ es       (h ∘ (e ∷_)) (f h) t
        → TyElims Γ (e ∷ es) h             s    t

{-# COMPILE AGDA2HS TyElims #-}
-}
