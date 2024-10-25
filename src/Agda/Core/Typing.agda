open import Scope
import Utils.List as List

open import Haskell.Prelude hiding (All; a; b; c; e; s; t; m)

open import Haskell.Extra.Erase
open import Haskell.Extra.Loop
open import Haskell.Law.Equality renaming (subst to transport)

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
  dataType d ds pars (subst (concatSubst (revSubst us) pars) (conIndices con))
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

  TyTVar : {x : NameIn α}

    ----------------------------------
    → Γ ⊢ TVar x ∶ lookupVar Γ x

  TyDef : {f : NameIn defScope}

    ----------------------------------------------
    → Γ ⊢ TDef f ∶ weaken subEmpty (getType sig f)

  TyData :
      {d : NameIn dataScope}
      {@0 p_subst : dataParScope d ⇒ α}
      {@0 i_subst : dataIxScope d ⇒ α}
      (let dt : Datatype (dataParScope d) (dataIxScope d)
           dt = sigData sig d)
    
    → TySubst Γ p_subst (weaken subEmpty (dataParameterTel dt))
    → TySubst Γ i_subst (substTelescope p_subst (dataIndexTel dt))
    ----------------------------------------------
    → Γ ⊢ dataTypeTerm d p_subst i_subst ∶ sortType (subst p_subst (dataSort dt))

  TyCon :
      {d : NameIn dataScope}
      {@0 pars : dataParScope d ⇒ α}
      (let dt : Datatype (dataParScope d) (dataIxScope d)
           dt = sigData sig d)
      {c : NameIn (dataConstructorScope dt)}
      (let (cp , con) = dataConstructors dt c)
      {@0 us : fieldScope (⟨ _ ⟩ cp) ⇒ α}
    
    → TySubst Γ us (substTelescope pars (conTelescope con))
    -----------------------------------------------------------
    → Γ ⊢ TCon (⟨ _ ⟩ cp) us ∶ constructorType d (⟨ _ ⟩ cp) con (subst pars (dataSort dt)) pars us

  TyLam :
    Γ , x ∶ a ⊢ u ∶ b
    -------------------------------
    → Γ ⊢ TLam x u ∶ El k (TPi x a b)

  TyApp : {b : Type α}

    → Γ ⊢ u ∶ El k (TPi x b c)
    → Γ ⊢ v ∶ b
    ------------------------------------
    → Γ ⊢ TApp u v ∶ substTop (rezz α) v c

  TyCase :
    {d : NameIn dataScope}                                        -- the name of a datatype
    (let p_scope = dataParScope d                                 -- parameters of d
         i_scope = dataIxScope d                                  -- indexes of d
         α' = ~ i_scope <> α                                      -- general scope + indexes
         dt = sigData sig d                                       -- the datatype called d
         α_run = rezz α                                           -- runtime general scope
         i_run = rezz i_scope)                                    -- runtime index scope
    {@0 p_subst : p_scope ⇒ α}                                    -- subst of parameters of d to α
    {@0 i_subst : i_scope ⇒ α}                                    -- subst of indexes of d to α
    (let i_subst' : i_scope ⇒ α'                                  -- subst of indexes of d to α'
         i_subst' = weaken (subJoinHere (rezz~ i_run) subRefl) (revIdSubst i_run)

         α'_subst : α' ⇒ α                                        -- subst of α' to α
         α'_subst = concatSubst (revSubst i_subst) (idSubst α_run))
    {cases : Branches α (dataConstructorScope dt)}                -- cases for constructors of dt
    {return : Type (x ◃ α')}                                      -- return type 
    (let α_In_α' : α ⊆ α'
         α_In_α' = subJoinDrop (rezz~ i_run) subRefl              -- proof that α is in α'

         Γ' : Context α'                                          -- new context with α and the indexes
         Γ' = addContextTel (substTelescope p_subst (dataIndexTel dt)) Γ

         tx : Type α'
         tx = dataType d (weaken α_In_α' k) (weaken α_In_α' p_subst) i_subst'

         return' : Type α
         return' = subst (SCons u α'_subst) return)

    → Γ' , x ∶ tx ⊢ unType return ∶ sortType (typeSort return) -- if return is well formed
    → TyBranches Γ dt p_subst return cases                     -- if each case is well typed
    → Γ ⊢ u ∶ dataType d k p_subst i_subst                     -- if u is well typed
    --------------------------------------------------
    → Γ ⊢ TCase d i_run u cases return ∶ return'               -- then the branching on u is well typed

  -- TODO: proj

  TyPi :
    Γ ⊢ u ∶ sortType k
    → Γ , x ∶ (El k u) ⊢ v ∶ sortType l
    ----------------------------------------------------------
    → Γ ⊢ TPi x (El k u) (El l v) ∶ sortType (piSort k l)

  TyType :

    -------------------------------------------
    Γ ⊢ TSort k ∶ sortType (sucSort k)

  TyLet : 
    Γ ⊢ u ∶ a
    → Γ , x ∶ a ⊢ v ∶ weakenType (subWeaken subRefl) b
    ----------------------------------------------
    → Γ ⊢ TLet x u v ∶ b

  TyAnn :
     Γ ⊢ u ∶ a
    ------------------
    → Γ ⊢ TAnn u a ∶ a

  TyConv :
    Γ ⊢ u ∶ a
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

data TyBranch {α} {x} Γ {p_scope} {i_scope} dt p_subst return where
  TyBBranch : (c : NameIn (dataConstructorScope dt))
              (let (c∈cons , con ) = dataConstructors dt c
                   fields = fieldScope (⟨ _ ⟩ c∈cons)
                   β = ~ fields <> α)
              {@0 r : Rezz fields}
              {@0 α_run : Rezz α}
              (rhs : Term β)
              (let rr = rezz~ r

                   Γ' : Context β
                   Γ' = addContextTel (substTelescope p_subst (conTelescope con)) Γ

                   cargs : fields ⇒ β
                   cargs = weaken (subJoinHere rr subRefl) (revIdSubst r)

                   parssubst : p_scope ⇒ β
                   parssubst = weaken (subJoinDrop rr subRefl) p_subst

                   parsAndArgsSubst : (~ fields <> p_scope) ⇒ β
                   parsAndArgsSubst = concatSubst (revSubst cargs) parssubst

                   ixsubst : i_scope ⇒ β
                   ixsubst = subst parsAndArgsSubst (conIndices con)

                   idsubst : α ⇒ β
                   idsubst = weaken (subJoinDrop rr subRefl) (idSubst α_run)

                   bsubst : (x ◃ (~ i_scope <> α)) ⇒ β
                   bsubst = SCons (TCon (⟨ _ ⟩ c∈cons) cargs) (concatSubst (revSubst ixsubst) idsubst)

                   return' : Type β
                   return' = subst bsubst return)

            → Γ' ⊢ rhs ∶ return'
            → TyBranch Γ dt p_subst return (BBranch (⟨ _ ⟩ c∈cons) r rhs)

{-# COMPILE AGDA2HS TyBranch #-}

data TySubst {α} Γ where
  TyNil  : TySubst Γ SNil EmptyTel
  TyCons : {@0 r : Rezz α}
         → Γ ⊢ u ∶ a
         → TySubst Γ us (substTelescope (SCons u (idSubst r)) tel)
         → TySubst Γ (SCons u us) (ExtendTel x a tel)

{-# COMPILE AGDA2HS TySubst #-}

{-  Helper functions to deal with erased signature in TypeChecker -}

tyData' : {@0 Γ : Context α} 
  {d : NameIn dataScope} 
  (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d ≡ dt
  → {@0 pars : dataParScope d ⇒ α}
  → {@0 ixs  : dataIxScope d  ⇒ α}
  → TySubst Γ pars (weaken subEmpty (dataParameterTel dt))
  → TySubst Γ ixs (substTelescope pars (dataIndexTel dt))
  ----------------------------------------------
  → Γ ⊢ dataTypeTerm d pars ixs ∶ sortType (subst pars (dataSort dt))
tyData' dt refl typars tyixs = TyData typars tyixs
{-# COMPILE AGDA2HS tyData' #-}


tyCon' : {@0 Γ : Context α} 
  {d : NameIn dataScope} 
  (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d ≡ dt
  → (c : NameIn (dataConstructorScope dt))
  → (let (cp , con) = dataConstructors dt c)
  → {@0 pars : dataParScope d ⇒ α}
  → {@0 us : fieldScope (⟨ _ ⟩ cp) ⇒ α}
  → TySubst Γ us (substTelescope pars (conTelescope con))
  ----------------------------------------------
  → Γ ⊢ TCon (⟨ _ ⟩ cp) us ∶ constructorType d (⟨ _ ⟩ cp) con (subst pars (dataSort dt)) pars us
tyCon' dt refl c tySubst = TyCon tySubst
{-# COMPILE AGDA2HS tyCon' #-}

tyApp' : {@0 Γ : Context α} {b : Type α} {c : Type (x ◃ α)} {@0 r : Rezz α}
  → Γ ⊢ u ∶ El k (TPi x b c)
  → Γ ⊢ v ∶ b
  ------------------------------------
  → Γ ⊢ TApp u v ∶ substTop {t = λ (@0 v) → Type v} r v c
tyApp' {r = rezz α} ty_u ty_v = TyApp ty_u ty_v

tyCase' : {@0 Γ : Context α} 
  {d : NameIn dataScope}
  (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d ≡ dt
   → (let p_scope = dataParScope d
          i_scope = dataIxScope d
          α' = ~ i_scope <> α)
  → {@0 α_run : Rezz α}
  {@0 i_run : Rezz i_scope}
  {@0 p_subst : p_scope ⇒ α}
  {@0 i_subst : i_scope ⇒ α}
  (let i_subst' = weaken (subJoinHere (rezz~ i_run) subRefl) (revIdSubst i_run)
       α'_subst = concatSubst (revSubst i_subst) (idSubst α_run))
  {cases : Branches α (dataConstructorScope dt)}
  {return : Type (x ◃ α')}
  (let α_In_α' = subJoinDrop (rezz~ i_run) subRefl
       Γ' = addContextTel (substTelescope p_subst (dataIndexTel dt)) Γ
       tx = dataType d (weaken α_In_α' k) (weaken α_In_α' p_subst) i_subst'
       return' = subst (SCons u α'_subst) return)
  → Γ' , x ∶ tx ⊢ unType return ∶ sortType (typeSort return)
  → TyBranches Γ dt p_subst return cases
  → Γ ⊢ u ∶ dataType d k p_subst i_subst
  --------------------------------------------------
  → Γ ⊢ TCase d i_run u cases return ∶ return'
tyCase' dt refl {α_run = α ⟨ refl ⟩} {i_run = i_scope ⟨ refl ⟩} wf_return ty_cases ty_u = 
  TyCase wf_return ty_cases ty_u
{-# COMPILE AGDA2HS tyCase' #-} 