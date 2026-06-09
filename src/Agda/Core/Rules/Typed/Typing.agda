open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
-- open import Agda.Core.Rules.Conversion

module Agda.Core.Rules.Typed.Typing
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x y z      : Name
  @0 α β γ     : Scope Name
  @0 rβ     : RScope Name
  @0 u v    : Term α
  @0 a b c  : Type α
  @0 k l    : Sort α



opaque
  unfolding Scope RScope
  lookupNameRinTel : (rs : Singleton α) (rrs : Singleton rβ) 
    (cargs : TermS α rβ) (tel : Telescope α rβ) (n : NameInR rβ) → Type α
  lookupNameRinTel _ _ _ EmptyTel x = nameInRemptyCase x
  lookupNameRinTel {α} rs ((_ ∷ rrs') ⟨ rrseq ⟩) (TSCons argTerm smallerTermS) (ExtendTel y typ smallerTel) x = 
    let 
      result : Type (α ▸ y)
      result = nameInRBindCase x 
        ((λ q → lookupNameRinTel 
          (singBind rs) (singTermS smallerTermS) (weakenTermS (subBindDrop subRefl) smallerTermS) smallerTel (⟨ _ ⟩ q))) 
        (λ proof → weakenType (subBindDrop subRefl) typ)
    in
    substTop rs argTerm result
  {-# COMPILE AGDA2HS lookupNameRinTel #-}


  -- isUnitType : Type α → Bool
  -- isUnitType (El typeSort₁ (TVar x)) = {!   !}
  -- isUnitType (El typeSort₁ (TDef d)) = {!   !}
  -- isUnitType (El typeSort₁ (TData d x x₁)) = {!   !}
  -- isUnitType (El (STyp zero) (TRec rn x)) = {!   !}
  -- isUnitType (El (STyp (suc x₁)) (TRec rn x)) = {!   !}
  -- isUnitType (El typeSort₁ (TDataCon c x)) = {!   !}
  -- isUnitType (El typeSort₁ (TRecCon r x)) = {!   !}
  -- isUnitType (El typeSort₁ (TLam x unType₁)) = {!   !}
  -- isUnitType (El typeSort₁ (TApp unType₁ unType₂)) = {!   !}
  -- isUnitType (El typeSort₁ (TProj unType₁ x)) = {!   !}
  -- isUnitType (El typeSort₁ (TCase d x unType₁ bs m)) = {!   !}
  -- isUnitType (El typeSort₁ (TPi x u v)) = {!   !}
  -- isUnitType (El typeSort₁ (TSort x)) = {!   !}
  -- isUnitType (El typeSort₁ (TLet x unType₁ unType₂)) = {!   !}
  -- isUnitType (El typeSort₁ (TAnn unType₁ t)) = {!   !}




dataConstructorType : {d : NameData}
                → (dt : Datatype d)
                → {c : NameDataCon d}
                → (con : DataConstructor c)
                → (pars : TermS α (dataParScope d))
                → TermS α (dataFieldScope c)
                → Type α
dataConstructorType {d = d} dt con pars us =
  dataType d (instDataSort dt pars) pars (instConIx con pars us)
{-# COMPILE AGDA2HS dataConstructorType #-}

recordConstructorType : {rn : NameRec}
              → (sigRec : Record rn)
              → TermS α (recParScope rn)
              → Type α
recordConstructorType {rn = rn} sigRec pars = El (instRecSort sigRec pars) (TRec rn pars)
{-# COMPILE AGDA2HS recordConstructorType #-}


-- opaque
--   unfolding RScope
--   etaProjTermS : {@0 rscope : RScope Name} → Singleton rscope → (NameInR rscope → Term α) → TermS α rscope
--   etaProjTermS ([] ⟨ refl ⟩)                   _  = TSNil
--   etaProjTermS ((Erased name ∷ names) ⟨ refl ⟩) f =
--     name ↦ f (⟨ name ⟩ inRHere) ◂ etaProjTermS (names ⟨ refl ⟩) (λ where (⟨ x ⟩ p) → f (⟨ x ⟩ inRThere p))
--   {-# COMPILE AGDA2HS etaProjTermS #-}

-- opaque
--   unfolding RScope


data IsUnitType : {@0 α : Scope Name} (@0 typ : Type α) → Set where
  TRecEmptyParsIsUnit : {@0 rn : NameRec} 
    (emptyPars : TermS α (recParScope rn))
    → ((recFieldScope rn) ≡ mempty) → IsUnitType (El (STyp 0) (TRec rn emptyPars))

-- IsUnitType : {@0 α : Scope Name} (@0 typ : Term α) → Set
-- IsUnitType rn = {!!}



data Conv      {@0 α} (@0 Γ : Context α) : @0 Term α → @0 Term α → @0 Type α → Set
data ConvTermS {@0 α} (@0 Γ : Context α) : (@0 rβ : RScope Name) → @0 TermS α rβ → @0 TermS α rβ → Set

data TyTerm  (@0 Γ : Context α) : @0 Term α     → @0 Type α         → Set

data TyTermS (@0 Γ : Context α) : @0 TermS α rβ → @0 Telescope α rβ → Set

data TyBranches (@0 Γ : Context α) {@0 d : NameData} (@0 dt : Datatype d)
                (@0 ps : TermS α (dataParScope d))
                (@0 rt : Type (α ◂▸ dataIxScope d ▸ x)) : {@0 cs : RScope (NameDataCon d)} → @0 Branches α d cs → Set

data TyBranch   (@0 Γ : Context α) {@0 d : NameData} (@0 dt : Datatype d)
                (@0 ps : TermS α (dataParScope d))
                (@0 rt : Type (α ◂▸ dataIxScope d ▸ x)) : {@0 c : NameDataCon d} → @0 Branch α c → Set

infix 3 TyTerm
syntax TyTerm Γ u t = Γ ⊢ u ∶ t
infix 3 TyTermS
syntax TyTermS Γ δ Δ = Γ ⊢ˢ δ ∶ Δ


infix 3 Conv
syntax Conv Γ x y t        = Γ ⊢ x ≅ y ∶ t
syntax ConvTermS Γ rscope us vs = Γ [ rscope ]  ⊢ us ⇔ vs 

renameTop : Singleton α → Term  (α ▸ x) → Term  (α ▸ y)
renameTop = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTop #-}

renameTopSort : Singleton α → Sort  (α ▸ x) → Sort  (α ▸ y)
renameTopSort = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopSort #-}

renameTopType : Singleton α → Type  (α ▸ x) → Type  (α ▸ y)
renameTopType = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopType #-}

data Conv {α} Γ where
  CRefl : {ty : Type α}
    → Γ ⊢ u ∶ ty
    → Γ ⊢ u ≅ u ∶ ty

  CLam : {@0 r : Singleton α}
    → CtxExtend Γ z a ⊢ renameTop {y = z} r u ≅ renameTop {y = z} r v ∶ b
    → Γ ⊢ TLam y u ≅ TLam z v ∶ El k (TPi z a b)

  -- ⊤ is unit type
  -- Γ ⊢ a ∶ ⊤
  -- Γ ⊢ b ∶ ⊤
  ------------
  -- Γ ⊢ a ≅ b
  CUnit : (tUnit : Type α)
          → IsUnitType tUnit
          → Γ ⊢ u ∶ tUnit
          → Γ ⊢ v ∶ tUnit
          → Γ ⊢ u ≅ v ∶ tUnit


data ConvTermS {α} Γ where
  CSNil : (us vs : TermS α mempty) → ConvTermS Γ mempty us vs
  CSCons : {@0 x : Name} {@0 rscope : RScope Name}
          (us vs : TermS α rscope) (ty : Type α)
          → Γ ⊢ u ≅ v ∶ ty
          → Γ [ rscope ] ⊢ us ⇔ vs
           → Γ [ rbind x rscope ] ⊢ (TSCons {x = x} u us) ⇔ (TSCons {x = x} v vs)




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
  
  TyRec : 
    {rn : NameRec}
    {@0 pars : TermS α (recParScope rn)}
    (let rt : Record rn
         rt = sigRecs sig rn)
    → Γ ⊢ˢ pars ∶ instRecParTel rt
    ----------------------------------------------
    → Γ ⊢ TRec rn pars ∶ sortType (instRecSort rt pars)

  TyDataCon :
      {d : NameData}
      {c : NameDataCon d}
      {@0 pars : TermS α (dataParScope d)}
      {@0 us  : TermS α (dataFieldScope c)}
      (let dt  : Datatype d
           dt  = sigData sig d
           con : DataConstructor c
           con = sigCons sig d c)

    → Γ ⊢ˢ us ∶ instConIndTel con pars
    -----------------------------------------------------------
    → Γ ⊢ TDataCon c us ∶ dataConstructorType dt con pars us

  TyRecCon : 
    {rn : NameRec}
    {@0 pars : TermS α (recParScope rn)}
    {@0 args : TermS α (recFieldScope rn)}
    (let sigRecord : Record rn
         sigRecord = sigRecs sig rn)
    → Γ ⊢ˢ args ∶ instRecConArgTel sigRecord pars
    -----------------------------------------------------------
    → Γ ⊢ TRecCon rn args ∶ recordConstructorType sigRecord pars

  TyLam :
      Γ , x ∶ a ⊢ u ∶ b
    -------------------------------
    → Γ ⊢ TLam x u ∶ El k (TPi x a b)

  TyApp : {b : Type α}

    → Γ ⊢ u ∶ El k (TPi x b c)
    → Γ ⊢ v ∶ b
    ------------------------------------
    → Γ ⊢ TApp u v ∶ substTop (singScope Γ) v c

  TyCase :
    {d : NameData}                                                -- the name of a datatype
    (let pScope = dataParScope d                                  -- parameters of d
         iScope = dataIxScope d                                   -- indexes of d
         α'     = α ◂▸ iScope                               -- general scope + indexes
         dt     = sigData sig d                                   -- the datatype called d
         iRun   = sing iScope)                                    -- runtime index scope
    {@0 pars : TermS α pScope}                                    -- parameters of d in Scope α
    {@0 ixs  : TermS α iScope}                                    -- indexes of d in Scope α
    (let ixs' : TermS α' iScope                                   -- indexes of d in Scope α'
         ixs' = weaken (subExtScope iRun subRefl) ixs
         α'Subst : α' ⇒ α                                         -- subst of α' to α
         α'Subst = extSubst (idSubst (singScope Γ)) ixs)
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

  TyProj : {rn : NameRec}
    {recordTerm : Term α}
    {rsort : Sort α}
    {projFunc : NameProj rn}
    {instPars : TermS α (recParScope rn)}
    (cargs : TermS α (recFieldScope rn))
    (let sigRecord : Record rn
         sigRecord = sigRecs sig rn)
    → Γ ⊢ recordTerm ∶ (El rsort (TRec rn instPars))
    → Γ ⊢ recordTerm ≅ (TRecCon rn cargs) ∶ (El rsort (TRec rn instPars))
    --------------------------------------------------------------------------
    → Γ ⊢ TProj recordTerm projFunc ∶ lookupNameRinTel (singScope Γ) (singTermS cargs) cargs (instRecConArgTel sigRecord instPars) projFunc

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

  -- TyConv :
  --     Γ ⊢ u ∶ a
  --   → Γ ⊢ unType a ≅ unType b
  --   ----------------
  --   → Γ ⊢ u ∶ b
    -- TODO: check that `b` is well-kinded?

{-# COMPILE AGDA2HS TyTerm #-}

data TyBranches {α} Γ {d} dt ps rt where
  TyBsNil : TyBranches Γ dt ps rt BsNil
  TyBsCons : ∀ {@0 c : NameDataCon d} {@0 cs : RScope (NameDataCon d)} {@0 b : Branch α c} {@0 bs : Branches α d cs}
           → TyBranch Γ dt ps rt b
           → TyBranches Γ dt ps rt bs
           → TyBranches Γ dt ps rt (BsCons b bs)

{-# COMPILE AGDA2HS TyBranches #-}

data TyBranch {α = α} {x} Γ {d = d} dt pars return where
  TyBBranch : (c : NameDataCon d)
              (let con : DataConstructor c
                   con = sigCons sig d c
                   fields = dataFieldScope c
                   α' = α ◂▸ fields
                   r = sing fields)
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
                   asubst = weaken (subExtScope r subRefl) (idSubst (singScope Γ))

                   bsubst : α ◂▸ dataIxScope d ▸ x ⇒ α'
                   -- (atejandev): Not sure why a TDataCon is used here
                   bsubst = (extSubst asubst ixs' ▹ x ↦ TDataCon c cargs)

                   return' : Type α'
                   return' = subst bsubst return)

            → Γ' ⊢ rhs ∶ return'
            → TyBranch Γ dt pars return (BBranch (sing c) r rhs)

{-# COMPILE AGDA2HS TyBranch #-}

data TyTermS {α} Γ where
  TyNil  :
    -----------------------------------------------------------
    Γ ⊢ˢ  ⌈⌉ ∶ ⌈⌉
  TyCons : {@0 us : TermS α rβ} {@0 Δ : Telescope (α ▸ x) rβ}
    → Γ ⊢ u ∶ a
    → Γ ⊢ˢ us ∶ substTelescope (idSubst (singScope Γ) ▹ x ↦ u) Δ
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

tyRec' : {@0 Γ : Context α}
  {rn : NameRec}
  (@0 rt : Record rn) → @0 sigRecs sig rn ≡ rt
  → {@0 pars : TermS α (recParScope rn)}
  → Γ ⊢ˢ pars ∶ instRecParTel rt
  ----------------------------------------------
  → Γ ⊢ TRec rn pars ∶ sortType (instRecSort rt pars)
tyRec' rt refl typars = TyRec typars
{-# COMPILE AGDA2HS tyRec' #-}

tyDataCon' : {@0 Γ : Context α}
  {d : NameData} → (@0 dt : Datatype d) → @0 sigData sig d ≡ dt
  → {c : NameDataCon d} (@0 con : DataConstructor c) → @0 sigCons sig d c ≡ con
  → {@0 pars : TermS α (dataParScope d)}
  → {@0 us : TermS α (dataFieldScope c)}
  → Γ ⊢ˢ us ∶ instConIndTel con pars
  ----------------------------------------------
  → Γ ⊢ TDataCon c us ∶ dataConstructorType dt con pars us
tyDataCon' dt refl con refl tySubst = TyDataCon tySubst
{-# COMPILE AGDA2HS tyDataCon' #-}

tyRecCon' : {@0 Γ : Context α}
  {rn : NameRec} → (@0 sigRecord : Record rn) → @0 sigRecs sig rn ≡ sigRecord
  → {@0 pars : TermS α (recParScope rn)}
  → {@0 args : TermS α (recFieldScope rn)}
  → Γ ⊢ˢ args ∶ instRecConArgTel sigRecord pars
  ----------------------------------------------
  → Γ ⊢ TRecCon rn args ∶ recordConstructorType sigRecord pars
tyRecCon' sigRecord refl tysubst = TyRecCon tysubst
{-# COMPILE AGDA2HS tyRecCon' #-}

tyCase' : {@0 Γ : Context α}
  {d : NameData}
  (@0 dt : Datatype d) → @0 sigData sig d ≡ dt
   → (let pScope = dataParScope d
          iScope = dataIxScope d
          α' = α ◂▸ iScope)
  → (let @0 αRun : Singleton α
         αRun = singScope Γ)
  {@0 iRun : Singleton iScope}
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



tyProj' : {@0 Γ : Context α}
  {rn : NameRec}
  {recordTerm : Term α}
  {rsort : Sort α}
  {projFunc : NameProj rn}
  (instPars : TermS α (recParScope rn))
  (cargs : TermS α (recFieldScope rn))
  (@0 sigRecord : Record rn) → @0 sigRecs sig rn ≡ sigRecord
  → Γ ⊢ recordTerm ∶ (El rsort (TRec rn instPars))
  → Γ ⊢ recordTerm ≅ (TRecCon rn cargs) ∶ (El rsort (TRec rn instPars))
  → Γ ⊢ TProj recordTerm projFunc ∶ lookupNameRinTel (singScope Γ) (singTermS cargs) cargs (instRecConArgTel sigRecord instPars) projFunc
tyProj' instPars cargs sigRecord refl proof1 proof2 = TyProj cargs proof1 proof2
{-# COMPILE AGDA2HS tyProj' #-}

tyBBranch' : {@0 Γ : Context α} {@0 d : NameData} {@0 dt : Datatype d}
            {@0 ps : TermS α (dataParScope d)}
            {@0 return : Type (α ◂▸ dataIxScope d ▸ x)}
            (c : NameDataCon d)
            (let fields = dataFieldScope c
                 β = α ◂▸ fields)
            (@0 con : DataConstructor c)
            → @0 sigCons sig d c ≡ con
            → {@0 r : Singleton fields}
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
                 idsubst = weakenSubst (subExtScope r subRefl) (idSubst (singScope Γ))

                 bsubst : α ◂▸ dataIxScope d ▸ x ⇒ β
                 bsubst = extSubst idsubst ixsubst ▹ x ↦ TDataCon c cargs

                 return' : Type β
                 return' = subst bsubst return)

          → Γ' ⊢ rhs ∶ return'
          → TyBranch Γ dt ps return (BBranch (sing c) r rhs)
tyBBranch' c0 con refl {r = sing fields} rsh crhs = TyBBranch c0 rsh crhs
{-# COMPILE AGDA2HS tyBBranch' #-}

-- These have to be here, see https://github.com/agda/agda2hs/issues/346
{-# COMPILE AGDA2HS Conv     #-}
{-# COMPILE AGDA2HS ConvTermS #-}