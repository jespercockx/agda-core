open import Scope
import Utils.List as List

open import Haskell.Prelude hiding (All; a; b; c; e; s; t; m)

open import Haskell.Extra.Erase
open import Haskell.Extra.Loop
open import Haskell.Law.Equality

open import Utils.Tactics using (auto)

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Signature
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.Conversion
open import Agda.Core.Context
open import Agda.Core.Substitute
open import Agda.Core.Utils

module Agda.Core.Typing
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x y con : Name
  @0 α β pars ixs cons : Scope Name
  @0 s t u v : Term α
  @0 a b c   : Type α
  @0 k l m   : Sort α
  @0 n       : Nat
  @0 tel     : Telescope α β
  @0 us vs   : α ⇒ β

constructorType : (d : NameIn dataScope)
                → (c : NameIn conScope)
                → (con : Constructor (dataParScope d) (dataIxScope d) c)
                → Sort α
                → (pars : dataParScope d ⇒ α)
                → fieldScope c ⇒ α
                → Type α
constructorType d c con ds pars us =
  dataType d ds pars (substSubst (concatSubst (revSubst us) pars) (conIndices con))
{-# COMPILE AGDA2HS constructorType #-}

data TyTerm (@0 Γ : Context α) : @0 Term α → @0 Type α → Set

data TySubst (@0 Γ : Context α) : @0 (β ⇒ α) → @0 Telescope α β → Set

data TyBranches (@0 Γ : Context α)
                {@0 pars ixs} (@0 dt : Datatype pars ixs)
                (@0 ps : pars ⇒ α)
                (@0 rt : Type (x ◃ (~ ixs <> α))) : @0 Branches α cons → Set

data TyBranch (@0 Γ : Context α)
              {@0 pars ixs} (@0 dt : Datatype pars ixs)
              (@0 ps : pars ⇒ α)
              (@0 rt : Type (x ◃ (~ ixs <> α))) : @0 Branch α con → Set

infix 3 TyTerm
syntax TyTerm Γ u t = Γ ⊢ u ∶ t

data TyTerm {α} Γ where

  TyTVar
    : (x : NameIn α)
    ----------------------------------
    → Γ ⊢ TVar x ∶ lookupVar Γ x

  TyDef
    : (f : NameIn defScope)
    ----------------------------------------------
    → Γ ⊢ TDef f ∶ weakenType subEmpty (getType sig f)

  TyData
    : (d : NameIn dataScope)
    → (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d ≡ dt
    → {@0 pars : dataParScope d ⇒ α}
    → {@0 ixs : dataIxScope d ⇒ α}
    → TySubst Γ pars (weakenTel subEmpty (dataParameterTel dt))
    → TySubst Γ ixs (substTelescope pars (dataIndexTel dt))
    ----------------------------------------------
    → Γ ⊢ dataTypeTerm d pars ixs ∶ sortType (substSort pars (dataSort dt))

  TyCon
    : (d : NameIn dataScope)
    → (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d ≡ dt
    → (c : NameIn (dataConstructorScope dt))
    → (let (cp , con) = dataConstructors dt c)
    → {@0 pars : dataParScope d ⇒ α}
    → {@0 us : fieldScope (⟨ _ ⟩ cp) ⇒ α}
    → TySubst Γ us (substTelescope pars (conTelescope con))
    -----------------------------------------------------------
    → Γ ⊢ TCon (⟨ _ ⟩ cp) us ∶ constructorType d (⟨ _ ⟩ cp) con (substSort pars (dataSort dt)) pars us

  TyLam
    : {@0 r : Rezz α}
    → Γ , x ∶ a ⊢ u ∶ renameTopType r b
    -------------------------------
    → Γ ⊢ TLam x u ∶ El k (TPi y a b)

  TyApp
    : {b : Type α} {@0 r : Rezz α}
    → Γ ⊢ u ∶ a
    → (unType a) ≅ TPi x b c
    → Γ ⊢ v ∶ b
    ------------------------------------
    → Γ ⊢ TApp u v ∶ substTopType r v c

  TyCase
    : {@0 r : Rezz α}
      (d : NameIn dataScope)
      (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d ≡ dt →
      {@0 ps : dataParScope d ⇒ α}
      {@0 is : dataIxScope d ⇒ α}
      (ri : Rezz (dataIxScope d))
      (bs : Branches α (dataConstructorScope dt))
      (rt : Type (x ◃ (~ dataIxScope d <> α)))
    → (let wk : Sub α (~ dataIxScope d <> α)
           wk = subJoinDrop (rezz~ ri) subRefl

           Γ' : Context (~ dataIxScope d <> α)
           Γ' = addContextTel (substTelescope ps (dataIndexTel dt)) Γ

           ixsubst : Subst (dataIxScope d) (~ dataIxScope d <> α)
           ixsubst = weakenSubst (subJoinHere (rezz~ ri) subRefl) (revIdSubst ri)

           tx : Type (~ dataIxScope d <> α)
           tx = dataType d (weakenSort wk k) (weakenSubst wk ps) ixsubst

           tret : Type α
           tret = substType (SCons u (concatSubst (revSubst is) (idSubst r))) rt)

    → Γ' , x ∶ tx ⊢ unType rt ∶ sortType (typeSort rt)
    → TyBranches Γ dt ps rt bs
    → Γ ⊢ u ∶ dataType d k ps is
    → Γ ⊢ TCase d ri u bs rt ∶ tret

  -- TODO: proj

  TyPi
    : Γ ⊢ u ∶ sortType k
    → Γ , x ∶ (El k u) ⊢ v ∶ sortType l
    ----------------------------------------------------------
    → Γ ⊢ TPi x (El k u) (El l v) ∶ sortType (piSort k l)

  TyType
    -------------------------------------------
    : Γ ⊢ TSort k ∶ sortType (sucSort k)

  TyLet
    : {@0 r : Rezz α}
    → Γ ⊢ u ∶ a
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
    -- TODO: check that `b` is well-kinded?

{-# COMPILE AGDA2HS TyTerm #-}

data TyBranches {α} Γ dt ps rt where
  TyBsNil : TyBranches Γ dt ps rt BsNil
  TyBsCons : ∀ {@0 b : Branch α con} {@0 bs : Branches α cons}
           → TyBranch Γ dt ps rt b
           → TyBranches Γ dt ps rt bs
           → TyBranches Γ dt ps rt (BsCons b bs)

{-# COMPILE AGDA2HS TyBranches #-}

data TyBranch {α} {x} Γ {pars} {ixs} dt ps rt where
  TyBBranch : (c : NameIn (dataConstructorScope dt))
            → (let (c∈cons , con ) = dataConstructors dt c
                   fields = fieldScope (⟨ _ ⟩ c∈cons)
                   β = ~ fields <> α)
            → {@0 r : Rezz fields}
              {@0 rα : Rezz α}
              (rhs : Term β)
              (let rr = rezz~ r

                   Γ' : Context β
                   Γ' = addContextTel (substTelescope ps (conTelescope con)) Γ

                   cargs : Subst fields β
                   cargs = weakenSubst (subJoinHere rr subRefl) (revIdSubst r)

                   parssubst : Subst pars β
                   parssubst = weakenSubst (subJoinDrop rr subRefl) ps

                   parsAndArgsSubst : Subst (~ fields <> pars) β
                   parsAndArgsSubst = concatSubst (revSubst cargs) parssubst

                   ixsubst : Subst ixs β
                   ixsubst = substSubst parsAndArgsSubst (conIndices con)

                   idsubst : Subst α β
                   idsubst = weakenSubst (subJoinDrop rr subRefl) (idSubst rα)

                   bsubst : Subst (x ◃ (~ ixs <> α)) β
                   bsubst = SCons (TCon (⟨ _ ⟩ c∈cons) cargs) (concatSubst (revSubst ixsubst) idsubst)

                   rt' : Type β
                   rt' = substType bsubst rt)

            → TyTerm Γ' rhs rt'
            → TyBranch Γ dt ps rt (BBranch (⟨ _ ⟩ c∈cons) r rhs)

{-# COMPILE AGDA2HS TyBranch #-}

data TySubst {α} Γ where
  TyNil  : TySubst Γ SNil EmptyTel
  TyCons : {@0 r : Rezz α}
         → TyTerm Γ u a
         → TySubst Γ us (substTelescope (SCons u (idSubst r)) tel)
         → TySubst Γ (SCons u us) (ExtendTel x a tel)

{-# COMPILE AGDA2HS TySubst #-}

