open import Haskell.Prelude hiding (All; a; b; c; e; s; t; m)
open import Haskell.Extra.Erase

open import Agda.Core.Name
open import Agda.Core.Utils
open import Agda.Core.Syntax
open import Agda.Core.Conversion

module Agda.Core.Typing
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x      : Name
  @0 α      : Scope Name
  @0 rβ     : RScope Name
  @0 u v    : Term α
  @0 a b c  : Type α
  @0 k l    : Sort α

constructorType : {d : NameData}
                → (dt : Datatype d)
                → {c : NameCon d}
                → (con : Constructor c)
                → (pars : TermS α (dataParScope d))
                → TermS α (fieldScope c)
                → Type α
constructorType {d = d} dt con pars us =
  dataType d (instDataSort dt pars) pars (instConIx con pars us)
{-# COMPILE AGDA2HS constructorType #-}

data TyTerm  (@0 Γ : Context α) : @0 Term α     → @0 Type α         → Set

data TyTermS (@0 Γ : Context α) : @0 TermS α rβ → @0 Telescope α rβ → Set

data TyBranches (@0 Γ : Context α) {@0 d : NameData} (@0 dt : Datatype d)
                (@0 ps : TermS α (dataParScope d))
                (@0 rt : Type ((extScope α (dataIxScope d)) ▸ x)) : {@0 cs : RScope (NameCon d)} → @0 Branches α d cs → Set

data TyBranch   (@0 Γ : Context α) {@0 d : NameData} (@0 dt : Datatype d)
                (@0 ps : TermS α (dataParScope d))
                (@0 rt : Type ((extScope α (dataIxScope d)) ▸ x)) : {@0 c : NameCon d} → @0 Branch α c → Set

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
      {d : NameData}
      {@0 pars : TermS α (dataParScope d)}
      {@0 ixs  : TermS α (dataIxScope  d)}
      (let dt  : Datatype d
           dt  = sigData sig d)

    → Γ ⊢ˢ pars ∶ instDataParTel dt
    → Γ ⊢ˢ ixs  ∶ instDataIxTel dt pars
    ----------------------------------------------
    → Γ ⊢ TData d pars ixs ∶ sortType (instDataSort dt pars)

  TyCon :
      {d : NameData}
      {c : NameCon d}
      {@0 pars : TermS α (dataParScope d)}
      {@0 us  : TermS α (fieldScope c)}
      (let dt  : Datatype d
           dt  = sigData sig d
           con : Constructor c
           con = sigCons sig d c)

    → Γ ⊢ˢ us ∶ instConIndTel con pars
    -----------------------------------------------------------
    → Γ ⊢ TCon c us ∶ constructorType dt con pars us

  TyLam :
      Γ , x ∶ a ⊢ u ∶ b
    -------------------------------
    → Γ ⊢ TLam x u ∶ El k (TPi x a b)

  TyApp : {b : Type α}

    → Γ ⊢ u ∶ El k (TPi x b c)
    → Γ ⊢ v ∶ b
    ------------------------------------
    → Γ ⊢ TApp u v ∶ substTop (rezzScope Γ) v c

  TyCase :
    {d : NameData}                                                -- the name of a datatype
    (let pScope = dataParScope d                                  -- parameters of d
         iScope = dataIxScope d                                   -- indexes of d
         α'     = extScope α iScope                               -- general scope + indexes
         dt     = sigData sig d                                   -- the datatype called d
         iRun   = rezz iScope)                                    -- runtime index scope
    {@0 pars : TermS α pScope}                                    -- parameters of d in Scope α
    {@0 ixs  : TermS α iScope}                                    -- indexes of d in Scope α
    (let ixs' : TermS α' iScope                                   -- indexes of d in Scope α'
         ixs' = weaken (subExtScope iRun subRefl) ixs
         α'Subst : α' ⇒ α                                         -- subst of α' to α
         α'Subst = extSubst (idSubst (rezzScope Γ)) ixs)
    {cases : Branches α d (AllNameCon d)}                         -- cases for constructors of dt
    {return : Type (α' ▸ x)}                                      -- return type
    (let αInα' : α ⊆ α'
         αInα' = subExtScope iRun subRefl                         -- proof that α is in α'
         Γ' : Context α'                                          -- new context with α and the indexes
         Γ' = addContextTel Γ (instDataIxTel dt pars)
         tx : Type α'
         tx = dataType d (weaken αInα' k) (weaken αInα' pars) ixs'
         return' : Type α
         return' = subst (α'Subst ▹ x ↦ u) return)

    → Γ' , x ∶ tx ⊢ unType return ∶ sortType (typeSort return)    -- if return is well formed
    → TyBranches Γ dt pars return cases                           -- if each case is well typed
    → Γ ⊢ u ∶ dataType d k pars ixs                               -- if u is well typed
    --------------------------------------------------
    → Γ ⊢ TCase d iRun u cases return ∶ return'                   -- then the branching on u is well typed

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
    → unType a ≅ unType b
    ----------------
    → Γ ⊢ u ∶ b
    -- TODO: check that `b` is well-kinded?

{-# COMPILE AGDA2HS TyTerm #-}

data TyBranches {α} Γ {d} dt ps rt where
  TyBsNil : TyBranches Γ dt ps rt BsNil
  TyBsCons : ∀ {@0 c : NameCon d} {@0 cs : RScope (NameCon d)} {@0 b : Branch α c} {@0 bs : Branches α d cs}
           → TyBranch Γ dt ps rt b
           → TyBranches Γ dt ps rt bs
           → TyBranches Γ dt ps rt (BsCons b bs)

{-# COMPILE AGDA2HS TyBranches #-}

data TyBranch {α = α} {x} Γ {d = d} dt pars return where
  TyBBranch : (c : NameCon d)
              (let con : Constructor c
                   con = sigCons sig d c
                   fields = fieldScope c
                   α' = extScope α fields
                   r = rezz fields)
              (rhs : Term α')
              (let Γ' : Context α'
                   Γ' = addContextTel Γ (instConIndTel con pars)

                   cargs : TermS α' fields
                   cargs = termSrepeat r

                   pars' : TermS α' (dataParScope d)
                   pars' = weaken (subExtScope r subRefl) pars

                   ixs' : TermS α' (dataIxScope d)
                   ixs' = instConIx con pars' cargs

                   asubst : α ⇒ α'
                   asubst = weaken (subExtScope r subRefl) (idSubst (rezzScope Γ))

                   bsubst : extScope α (dataIxScope d) ▸ x ⇒ α'
                   bsubst = (extSubst asubst ixs' ▹ x ↦ TCon c cargs)

                   return' : Type α'
                   return' = subst bsubst return)

            → Γ' ⊢ rhs ∶ return'
            → TyBranch Γ dt pars return (BBranch (rezz c) r rhs)

{-# COMPILE AGDA2HS TyBranch #-}

data TyTermS {α} Γ where
  TyNil  :
    -----------------------------------------------------------
    Γ ⊢ˢ  ⌈⌉ ∶ ⌈⌉
  TyCons : {@0 us : TermS α rβ} {@0 Δ : Telescope (α ▸ x) rβ}
    → Γ ⊢ u ∶ a
    → Γ ⊢ˢ us ∶ substTelescope (idSubst (rezzScope Γ) ▹ x ↦ u) Δ
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
  {d : NameData}
  (@0 dt : Datatype d) → @0 sigData sig d ≡ dt
  → {@0 pars : TermS α (dataParScope d)}
  → {@0 ixs  : TermS α (dataIxScope d)}
  → Γ ⊢ˢ pars ∶ instDataParTel dt
  → Γ ⊢ˢ ixs ∶ instDataIxTel dt pars
  ----------------------------------------------
  → Γ ⊢ TData d pars ixs ∶ sortType (instDataSort dt pars)
tyData' dt refl typars tyixs = TyData typars tyixs
{-# COMPILE AGDA2HS tyData' #-}


tyCon' : {@0 Γ : Context α}
  {d : NameData} → (@0 dt : Datatype d) → @0 sigData sig d ≡ dt
  → {c : NameCon d} (@0 con : Constructor c) → @0 sigCons sig d c ≡ con
  → {@0 pars : TermS α (dataParScope d)}
  → {@0 us : TermS α (fieldScope c)}
  → Γ ⊢ˢ us ∶ instConIndTel con pars
  ----------------------------------------------
  → Γ ⊢ TCon c us ∶ constructorType dt con pars us
tyCon' dt refl con refl tySubst = TyCon tySubst
{-# COMPILE AGDA2HS tyCon' #-}

tyCase' : {@0 Γ : Context α}
  {d : NameData}
  (@0 dt : Datatype d) → @0 sigData sig d ≡ dt
   → (let pScope = dataParScope d
          iScope = dataIxScope d
          α' = extScope α iScope)
  → (let @0 αRun : Rezz α
         αRun = rezzScope Γ)
  {@0 iRun : Rezz iScope}
  {@0 pSubst : TermS α pScope}
  {@0 iSubst : TermS α iScope}
  (let iSubst' = weakenTermS (subExtScope iRun subRefl) iSubst
       α'Subst = extSubst (idSubst αRun) iSubst)
  {cases : Branches α d (AllNameCon d)}
  {return : Type (α' ▸ x)}
  (let αInα' = subExtScope iRun subRefl
       Γ' =  addContextTel Γ (instDataIxTel dt pSubst)
       tx = dataType d (weaken αInα' k) (weaken αInα' pSubst) iSubst'
       return' = subst (α'Subst ▹ x ↦ u) return)
  → Γ' , x ∶ tx ⊢ unType return ∶ sortType (typeSort return)
  → TyBranches Γ dt pSubst return cases
  → Γ ⊢ u ∶ dataType d k pSubst iSubst
  --------------------------------------------------
  → Γ ⊢ TCase d iRun u cases return ∶ return'
tyCase' dt refl {iRun = iScope ⟨ refl ⟩} wfReturn tyCases tyu =
  TyCase wfReturn tyCases tyu
{-# COMPILE AGDA2HS tyCase' #-}

tyBBranch' : {@0 Γ : Context α} {@0 d : NameData} {@0 dt : Datatype d}
            {@0 ps : TermS α (dataParScope d)}
            {@0 return : Type ((extScope α (dataIxScope d)) ▸ x)}
            (c : NameCon d)
            (let fields = fieldScope c
                 β = extScope α fields)
            (@0 con : Constructor c)
            → @0 sigCons sig d c ≡ con
            → {@0 r : Rezz fields}
            (rhs : Term β)
            (let Γ' : Context β
                 Γ' = addContextTel Γ (instConIndTel con ps)

                 cargs : TermS β fields
                 cargs = termSrepeat r

                 parssubst : TermS β (dataParScope d)
                 parssubst = weakenTermS (subExtScope r subRefl) ps

                 ixsubst : TermS β (dataIxScope d)
                 ixsubst = instConIx con parssubst cargs

                 idsubst : α ⇒ β
                 idsubst = weakenSubst (subExtScope r subRefl) (idSubst (rezzScope Γ))

                 bsubst : extScope α (dataIxScope d) ▸ x ⇒ β
                 bsubst = extSubst idsubst ixsubst ▹ x ↦ TCon c cargs

                 return' : Type β
                 return' = subst bsubst return)

          → Γ' ⊢ rhs ∶ return'
          → TyBranch Γ dt ps return (BBranch (rezz c) r rhs)
tyBBranch' c0 con refl {r = rezz fields} rsh crhs = TyBBranch c0 rsh crhs
{-# COMPILE AGDA2HS tyBBranch' #-}
