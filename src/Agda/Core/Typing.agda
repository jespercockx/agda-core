open import Scope
import Utils.List as List

open import Agda.Core.GlobalScope using (Globals)
import Agda.Core.Signature as Signature

open import Haskell.Prelude hiding (All; a; b; c; d; e; s; t; m; f) renaming (_,_ to _,p_; _×_ to _×p_)

module Agda.Core.Typing
    {@0 name    : Set}
    (@0 globals : Globals name)
    (open Signature globals)
    (@0 sig     : Signature)
  where

private open module @0 G = Globals globals

open import Haskell.Extra.Erase
open import Haskell.Extra.Loop
open import Haskell.Law.Equality

open import Utils.Tactics using (auto)

open import Agda.Core.Syntax globals
open import Agda.Core.Reduce globals
open import Agda.Core.Conversion globals sig
open import Agda.Core.Context globals
open import Agda.Core.Substitute globals
open import Agda.Core.Utils --renaming (_,_ to _Σ,_)

private variable
  @0 x y c con f d : name
  @0 α β pars ixs cons : Scope name
  @0 s t u v : Term α
  @0 a b     : Type α
  @0 k l m   : Sort α
  @0 n       : Nat
  @0 e       : Elim α
  @0 tel     : Telescope α β
  @0 us vs   : α ⇒ β
  @0 r       : Rezz _ α

constructorType : (@0 d : name) (dp : d ∈ defScope)
                → (@0 c : name) (cp : c ∈ conScope)
                → (con : Constructor pars c cp)
                → Sort α
                → pars ⇒ α
                → fieldsOf cp ⇒ α
                → Type α
constructorType d dp c cp con ds pars us =
  dataType d dp ds pars
{-# COMPILE AGDA2HS constructorType #-}

data TyTerm (@0 Γ : Context α) : @0 Term α → @0 Type α → Set

-- TyElim Γ u e t a means: if  Γ ⊢ u : t  then  Γ ⊢ appE u e : a
data TyElim  (@0 Γ : Context α) : @0 Term α → @0 Elim α → @0 Type α → @0 Type α → Set

data TySubst (@0 Γ : Context α) : @0 (β ⇒ α) → @0 Telescope α β → Set

data TyBranches (@0 Γ : Context α) (@0 dt : Datatype)
                (@0 ps : dataPars dt ⇒ α)
                (@0 rt : Type (x ◃ α)) : @0 Branches α cons → Set

data TyBranch (@0 Γ : Context α) (@0 dt : Datatype)
              (@0 ps : dataPars dt ⇒ α)
              (@0 rt : Type (x ◃ α)) : @0 Branch α con → Set

infix 3 TyTerm
syntax TyTerm Γ u t = Γ ⊢ u ∶ t

{-# COMPILE AGDA2HS TyTerm #-}
{-# COMPILE AGDA2HS TyBranches #-}


data TyTerm {α} Γ where
  TyDef  : (@0 p : f ∈ defScope)
         → Γ ⊢ TDef f p ∶ weakenGlobalType (getType sig f p)
  TyCon :  (@0 dp : d ∈ defScope) (@0 dt : Datatype)
        →  (@0 cq : c ∈ dataCons dt)
        →   @0 getDefinition sig d dp ≡ DatatypeDef dt
        →  (let (cp , con) = lookupAll (dataConstructors dt) cq)
        →  {@0 pars : dataPars dt ⇒ α}
        →  {@0 us : fieldsOf cp ⇒ α}
        →  let ds = substSort pars (dataSort dt)
        in TySubst Γ us (substTelescope pars (conTelescope con))
        → Γ ⊢ TCon c cp us ∶ constructorType d dp c cp con ds pars us
  TyTVar
    : (@0 p : x ∈ α)
    ----------------------------------
    → Γ ⊢ TVar x p ∶ lookupVar Γ x p

  TyLam
    : Γ , x ∶ a ⊢ u ∶ renameTopType r b
    -------------------------------
    → Γ ⊢ TLam x u ∶ El k (TPi y a b)

  TyAppE
    : {b : Type α}
    → Γ ⊢ u ∶ a
    → TyElim Γ u e a b
    ------------------------------------
    → Γ ⊢ TApp u e ∶ b

  TyPi
    : Γ ⊢ u ∶ sortType k
    → Γ , x ∶ (El k u) ⊢ v ∶ sortType l
    ----------------------------------------------------------
    → Γ ⊢ TPi x (El k u) (El l v) ∶ sortType (piSort k l)

  TyType
    -------------------------------------------
    : Γ ⊢ TSort k ∶ sortType (sucSort k)

  TyLet
    : Γ ⊢ u ∶ a
    → Γ , x ∶ a ⊢ v ∶ weakenType (subWeaken subRefl) b
    ----------------------------------------------
    → Γ ⊢ TLet x u v ∶ b

  TyAnn
    : Γ ⊢ u ∶ a
    ------------------
    → Γ ⊢ TAnn u a ∶ a

  TyConv
    : Γ ⊢ u ∶ a
    → (unType a) ≅ (unType b)
    ----------------
    → Γ ⊢ u ∶ b

data TySubst {α} Γ where
  TyNil  : TySubst Γ SNil EmptyTel
  TyCons : TyTerm Γ u a
         → TySubst Γ us (substTelescope (SCons u (idSubst r)) tel)
         → TySubst Γ (SCons u us) (ExtendTel x a tel)
{-# COMPILE AGDA2HS TySubst #-}

data TyElim {α} Γ where
    TyCase : {@0 c : Type α}
             {@0 d : name} (@0 dp : d ∈ defScope) (@0 dt : Datatype)
             (@0 de : getDefinition sig d dp ≡ DatatypeDef dt)
             {@0 ps : dataPars dt ⇒ α}
             (bs : Branches α (dataCons dt))
             (rt : Type (x ◃ α))
           → (unType c) ≅ (unType $ dataType d dp k ps)
           → TyBranches Γ dt ps rt bs
           → TyElim Γ u (ECase bs rt) c (substTopType r u rt)

    TyArg : {@0 c : Type α}
          → (unType c) ≅ TPi x a b
          → Γ ⊢ v ∶ a
          → TyElim Γ u (EArg v) c (substTopType r v b)
{-# COMPILE AGDA2HS TyElim #-}

data TyBranches {α} Γ dt ps rt where
  TyBsNil : TyBranches Γ dt ps rt BsNil
  TyBsCons : {@0 b : Branch α con} {@0 bs : Branches α cons}
           → TyBranch Γ dt ps rt b → TyBranches Γ dt ps rt bs
           → TyBranches Γ dt ps rt (BsCons b bs)


data TyBranch {α} Γ dt ps rt where
  TyBBranch : (c∈dcons : c ∈ dataCons dt)
    → (let (c∈cons , con ) = lookupAll (dataConstructors dt) c∈dcons)
    → {@0 rf : Rezz _ (lookupAll fieldScope c∈cons)}
      {@0 r : Rezz _ α}
      (rhs : Term (~ fieldsOf c∈cons <> α))
      (let ctel = substTelescope ps (conTelescope con)
           cargs = weakenSubst (subJoinHere (rezzCong revScope rf) subRefl)
                               (revIdSubst rf)
           idsubst = weakenSubst (subJoinDrop (rezzCong revScope rf) subRefl)
                                 (idSubst r)
           bsubst = SCons (TCon c c∈cons cargs) idsubst)
    → TyTerm (addContextTel ctel Γ) rhs (substType bsubst rt)
    → TyBranch Γ dt ps rt (BBranch c c∈cons rf rhs)
{-# COMPILE AGDA2HS TyBranch #-}
