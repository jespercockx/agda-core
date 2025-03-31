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
  @0 rβ rγ : RScope Name
  @0 s t u v : Term α
  @0 a b c   : Type α
  @0 k l m   : Sort α
  @0 n       : Nat
  @0 Δ     : Telescope α rβ
  @0 us vs   : TermS α rβ

constructorType : (d : NameIn dataScope)
                → (c : NameIn conScope)
                → (con : Constructor (dataParScope d) (dataIxScope d) c)
                → Sort α
                → (pars : TermS α (dataParScope d))
                → TermS α (fieldScope c)
                → Type α
constructorType d c con ds pars us =
  dataType d ds pars (conIx con pars us)
{-# COMPILE AGDA2HS constructorType #-}

data TyTerm (@0 Γ : Context α) : @0 Term α → @0 Type α → Set

data TyTermS (@0 Γ : Context α) : @0 (TermS α rβ) → @0 Telescope α rβ → Set

data TyBranches (@0 Γ : Context α)
                {@0 pars ixs} (@0 dt : Datatype pars ixs)
                (@0 ps : TermS α pars)
                (@0 rt : Type ((extScope α ixs) ▸ x)) : @0 Branches α cons → Set

data TyBranch (@0 Γ : Context α)
              {@0 pars ixs} (@0 dt : Datatype pars ixs)
              (@0 ps : TermS α pars)
              (@0 rt : Type ((extScope α ixs) ▸ x)) : @0 Branch α con → Set

infix 3 TyTerm
syntax TyTerm Γ u t = Γ ⊢ u ∶ t
infix 3 TyTermS
syntax TyTermS Γ δ Δ = Γ ⊢ˢ δ ∶ Δ

data TyTerm {α} Γ where

  TyTVar : {x : NameIn α}

    ----------------------------------
    → Γ ⊢ TVar x ∶ lookupVar Γ x

  TyDef : {f : NameIn defScope}

    ----------------------------------------------
    → Γ ⊢ TDef f ∶ getType sig f

  TyData :
      {d : NameIn dataScope}
      {@0 pSubst : TermS α (dataParScope d)}
      {@0 iSubst : TermS α (dataIxScope d)}
      (let dt : Datatype (dataParScope d) (dataIxScope d)
           dt = sigData sig d)

    → Γ ⊢ˢ pSubst ∶ dataParTel dt
    → Γ ⊢ˢ iSubst ∶ dataIxTel dt pSubst
    ----------------------------------------------
    → Γ ⊢ TData d pSubst iSubst ∶ sortType (dataSort dt pSubst)

  TyCon :
      {d : NameIn dataScope}
      {@0 pars : TermS α (dataParScope d)}
      (let dt : Datatype (dataParScope d) (dataIxScope d)
           dt = sigData sig d)
      {c : NameIn (dataConstructorScope dt)}
      (let (cp , con) = dataConstructors dt c)
      {@0 us : TermS α (fieldScope (⟨ _ ⟩ cp))}

    → Γ ⊢ˢ us ∶ conIndTel con pars
    -----------------------------------------------------------
    → Γ ⊢ TCon (⟨ _ ⟩ cp) us ∶ constructorType d (⟨ _ ⟩ cp) con (dataSort dt pars) pars us

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
    (let pScope = dataParScope d                                 -- parameters of d
         iScope = dataIxScope d                                  -- indexes of d
         α' = extScope α iScope                                  -- general scope + indexes
         dt = sigData sig d                                       -- the datatype called d
         αRun = rezz α                                           -- runtime general scope
         iRun = rezz iScope)                                     -- runtime index scope
    {@0 pSubst : TermS α pScope}                                    -- subst of parameters of d to α
    {@0 iSubst : TermS α iScope}                                    -- subst of indexes of d to α
    (let iSubst' : TermS α' iScope                                  -- subst of indexes of d to α'
         iSubst' = weaken (subExtScope iRun subRefl) iSubst

         α'Subst : α' ⇒ α                                        -- subst of α' to α
         α'Subst = extSubst (idSubst αRun) iSubst)
    {cases : Branches α (dataConstructorScope dt)}                -- cases for constructors of dt
    {return : Type (α' ▸ x)}                                      -- return type
    (let αInα' : α ⊆ α'
         αInα' = subExtScope iRun subRefl              -- proof that α is in α'

         Γ' : Context α'                                          -- new context with α and the indexes
         Γ' = addContextTel Γ (dataIxTel dt pSubst)

         tx : Type α'
         tx = dataType d (weaken αInα' k) (weaken αInα' pSubst) iSubst'

         return' : Type α
         return' = subst (α'Subst ▹ x ↦ u) return)

    → Γ' , x ∶ tx ⊢ unType return ∶ sortType (typeSort return) -- if return is well formed
    → TyBranches Γ dt pSubst return cases                     -- if each case is well typed
    → Γ ⊢ u ∶ dataType d k pSubst iSubst                     -- if u is well typed
    --------------------------------------------------
    → Γ ⊢ TCase d iRun u cases return ∶ return'               -- then the branching on u is well typed

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
    → Γ , x ∶ a ⊢ v ∶ weakenType (subBindDrop subRefl) b
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

data TyBranch {α} {x} Γ {pScope} {iScope} dt pSubst return where
  TyBBranch : (c : NameIn (dataConstructorScope dt))
              (let (c∈cons , con ) = dataConstructors dt c
                   fields = fieldScope (⟨ _ ⟩ c∈cons)
                   β = extScope α fields)
              {@0 r : Rezz fields} {- TODO: remove Rezz via helper function -}
              {@0 αRun : Rezz α}
              (rhs : Term β)
              (let Γ' : Context β
                   Γ' = addContextTel Γ (conIndTel con pSubst)

                   cargs : TermS β fields
                   cargs = termSrepeat r

                   parssubst : TermS β pScope
                   parssubst = weaken (subExtScope r subRefl) pSubst

                   ixsubst : TermS β iScope
                   ixsubst = conIx con parssubst cargs

                   idsubst : α ⇒ β
                   idsubst = weaken (subExtScope r subRefl) (idSubst αRun)

                   bsubst : extScope α iScope ▸ x ⇒ β
                   bsubst = (extSubst idsubst ixsubst ▹ x ↦ TCon (⟨ _ ⟩ c∈cons) cargs)

                   return' : Type β
                   return' = subst bsubst return)

            → Γ' ⊢ rhs ∶ return'
            → TyBranch Γ dt pSubst return (BBranch (⟨ _ ⟩ c∈cons) r rhs)

{-# COMPILE AGDA2HS TyBranch #-}

data TyTermS {α} Γ where
  TyNil  :
    -----------------------------------------------------------
    Γ ⊢ˢ  ⌈⌉ ∶ ⌈⌉
  TyCons :
    Γ ⊢ u ∶ a
    → Γ ⊢ˢ us ∶ substTelescope (idSubst (rezz α) ▹ x ↦ u) Δ
    -----------------------------------------------------------
    → Γ ⊢ˢ (x ↦ u ◂ us) ∶ (x ∶ a ◂ Δ)

{-# COMPILE AGDA2HS TyTermS #-}

{-  Helper functions to deal with erased signature in TypeChecker -}

tyDef' : {@0 Γ : Context α}
  {f : NameIn defScope}
  (@0 ty : Type α) → @0 getType sig f ≡ ty
  ----------------------------------------------
  → Γ ⊢ TDef f ∶ ty
tyDef' ty refl = TyDef
{-# COMPILE AGDA2HS tyDef' #-}

tyData' : {@0 Γ : Context α}
  {d : NameIn dataScope}
  (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d ≡ dt
  → {@0 pars : TermS α (dataParScope d)}
  → {@0 ixs  : TermS α (dataIxScope d)}
  → Γ ⊢ˢ pars ∶ dataParTel dt
  → Γ ⊢ˢ ixs ∶ dataIxTel dt pars
  ----------------------------------------------
  → Γ ⊢ TData d pars ixs ∶ sortType (dataSort dt pars)
tyData' dt refl typars tyixs = TyData typars tyixs
{-# COMPILE AGDA2HS tyData' #-}


tyCon' : {@0 Γ : Context α}
  {d : NameIn dataScope}
  (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d ≡ dt
  → (c : NameIn (dataConstructorScope dt))
  → (let (cp , con) = dataConstructors dt c)
  → {@0 pars : TermS α (dataParScope d)}
  → {@0 us : TermS α (fieldScope (⟨ _ ⟩ cp))}
  → Γ ⊢ˢ us ∶ conIndTel con pars
  ----------------------------------------------
  → Γ ⊢ TCon (⟨ _ ⟩ cp) us ∶ constructorType d (⟨ _ ⟩ cp) con (dataSort dt pars) pars us
tyCon' dt refl c tySubst = TyCon tySubst
{-# COMPILE AGDA2HS tyCon' #-}

tyApp' : {@0 Γ : Context α} {b : Type α} {c : Type  (α ▸ x)} {@0 r : Rezz α}
  → Γ ⊢ u ∶ El k (TPi x b c)
  → Γ ⊢ v ∶ b
  ------------------------------------
  → Γ ⊢ TApp u v ∶ substTop {t = λ (@0 v) → Type v} r v c
tyApp' {r = rezz α} tyu tyv = TyApp tyu tyv
{-# COMPILE AGDA2HS tyApp' #-}

tyCase' : {@0 Γ : Context α}
  {d : NameIn dataScope}
  (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d ≡ dt
   → (let pScope = dataParScope d
          iScope = dataIxScope d
          α' = extScope α iScope)
  → {@0 αRun : Rezz α}
  {@0 iRun : Rezz iScope}
  {@0 pSubst : TermS α pScope}
  {@0 iSubst : TermS α iScope}
  (let iSubst' = weakenTermS (subExtScope iRun subRefl) iSubst
       α'Subst = extSubst (idSubst αRun) iSubst)
  {cases : Branches α (dataConstructorScope dt)}
  {return : Type (α' ▸ x)}
  (let αInα' = subExtScope iRun subRefl
       Γ' =  addContextTel Γ (dataIxTel dt pSubst)
       tx = dataType d (weaken αInα' k) (weaken αInα' pSubst) iSubst'
       return' = subst (α'Subst ▹ x ↦ u) return)
  → Γ' , x ∶ tx ⊢ unType return ∶ sortType (typeSort return)
  → TyBranches Γ dt pSubst return cases
  → Γ ⊢ u ∶ dataType d k pSubst iSubst
  --------------------------------------------------
  → Γ ⊢ TCase d iRun u cases return ∶ return'
tyCase' dt refl {αRun = α ⟨ refl ⟩} {iRun = iScope ⟨ refl ⟩} wfReturn tyCases tyu =
  TyCase wfReturn tyCases tyu
{-# COMPILE AGDA2HS tyCase' #-}

tyCons' : {@0 Γ : Context α} {@0 αRun : Rezz α}
  → Γ ⊢ u ∶ a
  → Γ ⊢ˢ us ∶ (substTelescope (idSubst αRun ▹ x ↦ u) Δ)
  -----------------------------------------------------------
  → Γ ⊢ˢ (x ↦ u ◂ us) ∶ (x ∶ a ◂ Δ)
tyCons' {αRun = α ⟨ refl ⟩} tyu tyus = TyCons tyu tyus
{-# COMPILE AGDA2HS tyCons' #-}
