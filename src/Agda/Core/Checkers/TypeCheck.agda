open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.Rules.Conversion
open import Agda.Core.Rules.Typing
open import Agda.Core.TCM.Instances
open import Agda.Core.Checkers.Converter
open import Agda.Core.Syntax.Weakening 

module Agda.Core.Checkers.TypeCheck
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x : Name
  @0 α : Scope Name
  @0 rβ : RScope Name

checkCoerce : ∀ Γ (t : Term α)
            → Σ[ ty ∈ Type α ] Γ ⊢ t ∶ ty
            → (cty : Type α)
            → TCM (Γ ⊢ t ∶ cty)
checkCoerce ctx t (gty , dgty) cty = do
  let r = singScope ctx
  TyConv dgty <$> convert r (unType gty) (unType cty)
{-# COMPILE AGDA2HS checkCoerce #-}

tcmGetType : (x : NameIn defScope) → TCM (Singleton (getType {α = α} sig x))
tcmGetType x = do
  rsig ← tcmSignature
  return (singCong (λ sig → getType sig x) rsig)
{-# COMPILE AGDA2HS tcmGetType #-}

tcmGetDefinition : (x : NameIn defScope) → TCM (Singleton (getDefinition sig x))
tcmGetDefinition x = do
  rsig ← tcmSignature
  return (singCong (λ sig → getDefinition sig x) rsig)
{-# COMPILE AGDA2HS tcmGetDefinition #-}

tcmGetDatatype : (d : NameData) → TCM (Singleton (sigData sig d))
tcmGetDatatype d = do
  rsig ← tcmSignature
  return (singCong (λ sig → sigData sig d) rsig)
{-# COMPILE AGDA2HS tcmGetDatatype #-}

tcmGetRecord : (rn : NameRec) → TCM (Singleton (sigRecs sig rn))
tcmGetRecord rn = do
  rsig ← tcmSignature
  return (singCong (λ sig → sigRecs sig rn) rsig)
{-# COMPILE AGDA2HS tcmGetRecord #-}

tcmGetConstructor : {d : NameData} (c : NameCon d) → TCM (Singleton (sigCons sig d c))
tcmGetConstructor {d = d} c = do
  rsig ← tcmSignature
  return (singCong (λ sig → sigCons sig d c) rsig)
{-# COMPILE AGDA2HS tcmGetConstructor #-}

inferVar : ∀ Γ (x : NameIn α) → TCM (Σ[ t ∈ Type α ] Γ ⊢ TVar x ∶ t)
inferVar ctx x = return $ _ , TyTVar
{-# COMPILE AGDA2HS inferVar #-}

inferSort : (Γ : Context α) (t : Term α) → TCM (Σ[ s ∈ Sort α ] Γ ⊢ t ∶ sortType s)
inferType : ∀ (Γ : Context α) u → TCM (Σ[ t ∈ Type α ] Γ ⊢ u ∶ t)
checkType : ∀ (Γ : Context α) u (ty : Type α) → TCM (Γ ⊢ u ∶ ty)
checkBranches : ∀ {d : NameData} {@0 cons : RScope (NameCon d)}
                  (Γ : Context α)
                  (rz : Singleton cons)
                  (bs : Branches α d cons)
                  (dt : Datatype d)
                  (ps : TermS α (dataParScope d))
                  (rt : Type (α ◂▸ dataIxScope d ▸ x))
                → TCM (TyBranches Γ dt ps rt bs)

inferApp : ∀ Γ u v → TCM (Σ[ t ∈ Type α ] Γ ⊢ TApp u v ∶ t)
inferApp ctx u v = do
  let r = singScope ctx
  tu , gtu ← inferType ctx u
  ⟨ x ⟩ (at , rt) ⟨ rtp ⟩ ← reduceToPi r (unType tu)
    "couldn't reduce term to a pi type"
  gtv ← checkType ctx v at
  let tytype = substTop r v rt
      gc = CRedL rtp CRefl
      gtu' =  TyConv {b = El (typeSort tu) (TPi x at rt)} gtu gc
  return (tytype , TyApp gtu' gtv)
{-# COMPILE AGDA2HS inferApp #-}

inferCase : ∀ Γ d r u bs rt → TCM (Σ[ t ∈ Type α ] Γ ⊢ TCase {x = x} d r u bs rt ∶ t)
inferCase {α = α} ctx d rixs u bs rt = do
  let r = singScope ctx

  El s tu , gtu ← inferType ctx u
  d' , (params , ixs) ⟨ rp ⟩ ← reduceToData r tu
    "can't typecheck a constructor with a type that isn't a def application"
  Erased refl ← convNamesIn d d'
  df ⟨ deq ⟩ ← tcmGetDatatype d
  let ds : Sort α
      ds = instDataSort df params
      gtu' : ctx ⊢ u ∶ dataType d ds params ixs
      gtu' = TyConv gtu (CRedL rp CRefl)

  grt ← checkType (_ , _ ∶ weaken (subExtScope rixs subRefl) (dataType d ds params ixs)) (unType rt) (sortType (typeSort rt))

  -- Erased refl ← checkCoverage df bs
  cb ← checkBranches ctx (singBranches bs) bs df params rt

  return (_ , tyCase' {k = ds} df deq {iRun = rixs} grt cb gtu')

{-# COMPILE AGDA2HS inferCase #-}

inferProj : {rn : NameRec} (Γ : Context α) (recordTerm : Term α) (projFunc : NameProj rn) →
  TCM (Σ[ t ∈ Type α ] Γ ⊢ TProj recordTerm projFunc ∶ t)
inferProj {rn = rn} ctx recordTerm projFunc = do
  let r = singScope ctx

  El rsort typeOfRecordTerm , typDerivRecTerm ← inferType ctx recordTerm
  rn' , params ⟨ rp ⟩  ← reduceToRec r typeOfRecordTerm "cannot type check a projection that is not of a record type"
  ifDec (decIn (proj₂ rn) (proj₂ rn'))
    (λ where {{refl}} → do
      coercedTypingDeriv ← checkCoerce ctx recordTerm ( (El rsort typeOfRecordTerm), typDerivRecTerm ) (El rsort (TRec rn params))
      sigRecord ⟨ defeq ⟩ ← tcmGetRecord rn
      let projFuncType = lookupVarInTel (instRecConArgTel sigRecord params) projFunc
      return ( projFuncType ,  tyProj' params sigRecord defeq coercedTypingDeriv)
    )
    (tcError "not convertible")
{-# COMPILE AGDA2HS inferProj #-}

inferPi
  : ∀ Γ (@0 x : Name)
  (a : Type α)
  (b : Type  (α ▸ x))
  → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TPi x a b ∶ ty)
inferPi ctx x (El su u) (El sv v) = do
  tu <- checkType ctx u (sortType su)
  tv <- checkType (ctx , x ∶ El su u) v (sortType sv)
  let spi = piSort su sv
  return $ sortType spi , TyPi tu tv
{-# COMPILE AGDA2HS inferPi #-}

inferTySort : ∀ Γ (s : Sort α) → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TSort s ∶ ty)
inferTySort ctx (STyp x) = return $ sortType (sucSort (STyp x)) , TyType
{-# COMPILE AGDA2HS inferTySort #-}

inferDef : ∀ Γ (f : NameIn defScope)
         → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TDef f ∶ ty)
inferDef ctx f = do
  ty ⟨ eq ⟩ ← tcmGetType f
  return $ ty , tyDef' ty eq
{-# COMPILE AGDA2HS inferDef #-}

checkTermS : ∀ {@0 α rβ} Γ (t : Telescope α rβ) (s : TermS α rβ) → TCM (Γ ⊢ˢ s ∶ t)
checkTermS ctx ⌈⌉ t =
  caseTermSNil t (λ where ⦃ refl ⦄ → return TyNil)
checkTermS {α = α} ctx (ExtendTel {rβ = rβ} x ty rest) ts =
  caseTermSCons ts (λ where
    u s ⦃ refl ⦄ → do
      tyx ← checkType ctx u ty
      let r = singScope ctx
          stel : Telescope α rβ
          stel = substTelescope (idSubst r ▹ x ↦ u) rest
      tyrest ← checkTermS ctx stel s
      return (TyCons tyx tyrest))
{-# COMPILE AGDA2HS checkTermS #-}

inferData : (Γ : Context α) (d : NameData)
          → (pars : TermS α (dataParScope d)) (ixs : TermS α (dataIxScope d))
          → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TData d pars ixs ∶ ty)
inferData ctx d pars ixs = do
  dt ⟨ deq ⟩ ← tcmGetDatatype d
  typars ← checkTermS ctx (instDataParTel dt) pars
  tyixs ← checkTermS ctx (instDataIxTel dt pars) ixs
  return (sortType (instDataSort dt pars) , tyData' dt deq typars tyixs)
{-# COMPILE AGDA2HS inferData #-}

inferRec : (Γ : Context α) (rn : NameRec)
          → (pars : TermS α (recParScope rn))
          → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TRec rn pars ∶ ty)
inferRec ctx rn pars = do
  rt ⟨ defeq ⟩ ← tcmGetRecord rn
  typars ← checkTermS ctx (instRecParTel rt) pars
  return (sortType (instRecSort rt pars) , tyRec' rt defeq typars)
{-# COMPILE AGDA2HS inferRec #-}

checkBranch : ∀ {d : NameData} {@0 con : NameCon d} (Γ : Context α)
                (bs : Branch α con)
                (dt : Datatype d)
                (ps : TermS α (dataParScope d))
                (rt : Type (α ◂▸ dataIxScope d ▸ x))
            → TCM (TyBranch Γ dt ps rt bs)
checkBranch {α = α} {d = d} ctx (BBranch (sing c) r rhs) dt ps rt = do
  -- cid ⟨ refl ⟩  ← liftMaybe (getConstructor c dt)
    -- "can't find a constructor with such a name"
  con ⟨ ceq ⟩ ← tcmGetConstructor c
  let ra = singScope ctx
      @0 β : Scope Name
      β = α ◂▸ dataFieldScope c
      cargs : TermS β (dataFieldScope c)
      cargs = termSrepeat r
      parssubst : TermS β (dataParScope d)
      parssubst = weaken (subExtScope r subRefl) ps
      ixsubst : TermS β (dataIxScope d)
      ixsubst = instConIx con parssubst cargs
      idsubst : α ⇒ β
      idsubst = weaken (subExtScope r subRefl) (idSubst ra)
      bsubst : α ◂▸ dataIxScope d ▸ x ⇒ β
      bsubst = extSubst idsubst ixsubst ▹ _ ↦ TDataCon c cargs
      rt' :  Type β
      rt' = subst bsubst rt
  crhs ← checkType _ rhs rt'
  return (tyBBranch' c con ceq {r = r} rhs crhs)
{-# COMPILE AGDA2HS checkBranch #-}

checkBranches {d = d} ctx (sing cons) bs dt ps rt =
  caseRScope cons
    (λ where {{refl}} → caseBsNil bs (λ where {{refl}} → return TyBsNil))
    (λ ch ct → λ where
      {{refl}} → caseBsCons bs (λ bh bt → λ where
        {{refl}} → TyBsCons <$> checkBranch {d = d} ctx bh dt ps rt
                            <*> checkBranches ctx (singBranches bt) bt dt ps rt))
{-# COMPILE AGDA2HS checkBranches #-}

checkDataCon : ∀ Γ
           {d : NameData}
           (c : NameCon d)
           (cargs : TermS α (dataFieldScope c))
           (ty : Type α)
         → TCM (Γ ⊢ TDataCon c cargs ∶ ty)
checkDataCon ctx {d = d} c cargs (El s ty) = do
  let r = singScope ctx
  d' , (params , ixs) ⟨ rp ⟩ ← reduceToData r ty
    "can't typecheck a constructor TDataCon with a type that isn't a TData"
  ifDec (decIn (proj₂ d) (proj₂ d'))
    (λ where {{refl}} → do
        dt ⟨ dteq ⟩ ← tcmGetDatatype d
        -- cid ⟨ refl ⟩  ← liftMaybe (getConstructor c dt)
          -- "can't find a constructor with such a name"
        con ⟨ ceq ⟩ ← tcmGetConstructor c
        let ctel = instConIndTel con params
            ctype = dataConstructorType dt con params cargs
        tySubst ← checkTermS ctx ctel cargs

        -- Check whether `ctype` can be converted to `El s ty`
        checkCoerce ctx (TDataCon c cargs) (ctype , tyDataCon' dt dteq con ceq tySubst) (El s ty))
    (tcError "datatypes not convertible")
{-# COMPILE AGDA2HS checkDataCon #-}

checkRecCon : ∀ Γ 
          (rn : NameRec)
          (cargs : TermS α (recFieldScope rn))
          (ty : Type α)
        → TCM (Γ ⊢ (TRecCon rn cargs) ∶ ty)
checkRecCon ctx rn cargs (El s ty) = do
  let r = singScope ctx
  rn' , params ⟨ rp ⟩ ← reduceToRec r ty 
    "can't typecheck a constructor TRecCon with a type that isn't a TRec"
  ifDec (decIn (proj₂ rn) (proj₂ rn'))
    (λ where {{refl}} → do
      rec ⟨ receq ⟩ ← tcmGetRecord rn
      
      let ctype = recordConstructorType rec params


      let ctel = instRecConArgTel rec params
      tySubst ← checkTermS ctx ctel cargs

      checkCoerce ctx (TRecCon rn cargs) ( ctype , tyRecCon' rec receq tySubst) (El s ty)
    )
    (tcError "record types not convertible")
{-# COMPILE AGDA2HS checkRecCon #-}


checkLambda : ∀ Γ (@0 x : Name)
              (u : Term  (α ▸ x))
              (ty : Type α)
              → TCM (Γ ⊢ TLam x u ∶ ty)
checkLambda ctx x u (El s ty) = do
  let r = singScope ctx

  -- TODO: introduce helper function to avoid pattern match on codomain
  ⟨ y ⟩ (tu , El tvs tvt) ⟨ rtp ⟩ ← reduceToPi r ty
    "couldn't reduce a term to a pi type"

  d ← checkType (ctx , x ∶ tu) u (El (renameTopSort r tvs) (renameTop r tvt))

  let gc = CRedR rtp (CPi CRefl CRefl)
      sp = piSort (typeSort tu) tvs

  return $ TyConv (TyLam {k = sp} d) gc

{-# COMPILE AGDA2HS checkLambda #-}

checkLet : ∀ Γ (@0 x : Name)
           (u : Term α)
           (v : Term  (α ▸ x))
           (ty : Type α)
           → TCM (Γ ⊢ TLet x u v ∶ ty)
checkLet ctx x u v ty = do
  tu , dtu  ← inferType ctx u
  dtv       ← checkType (ctx , x ∶ tu) v (weaken (subBindDrop subRefl) ty)
  return $ TyLet dtu dtv
{-# COMPILE AGDA2HS checkLet #-}


checkType ctx (TVar x) ty = do
  tvar ← inferVar ctx x
  checkCoerce ctx (TVar x) tvar ty
checkType ctx (TDef d) ty = do
  tdef ← inferDef ctx d
  checkCoerce ctx (TDef d) tdef ty
checkType ctx (TData d ps is) ty = do
  tdef ← inferData ctx d ps is
  checkCoerce ctx (TData d ps is) tdef ty
checkType ctx (TRec rn pars) ty = do
  trec ← inferRec ctx rn pars
  checkCoerce ctx (TRec rn pars) trec ty
checkType ctx (TDataCon c x) ty = checkDataCon ctx c x ty
checkType ctx (TRecCon rec x) ty = checkRecCon ctx rec x ty
checkType ctx (TLam x te) ty = checkLambda ctx x te ty
checkType ctx (TApp u e) ty = do
  tapp ← inferApp ctx u e
  checkCoerce ctx (TApp u e) tapp ty
checkType ctx (TCase d r u bs rt) ty = do
  tapp ← inferCase ctx d r u bs rt
  checkCoerce ctx (TCase d r u bs rt) tapp ty
checkType ctx (TProj rt projFunc) ty = tcError "TODO"
  -- do
  --   tproj ← inferProj ctx rt projFunc
  --   checkCoerce ctx (TProj rt projFunc) tproj ty
checkType ctx (TPi x tu tv) ty = do
  tpi ← inferPi ctx x tu tv
  checkCoerce ctx (TPi x tu tv) tpi ty
checkType ctx (TSort s) ty = do
  tts ← inferTySort ctx s
  checkCoerce ctx (TSort s) tts ty
checkType ctx (TLet x u v) ty = checkLet ctx x u v ty
checkType ctx (TAnn u t) ty = do
  ct ← TyAnn <$> checkType ctx u t
  checkCoerce ctx (TAnn u t) (t , ct) ty

{-# COMPILE AGDA2HS checkType #-}

inferType ctx (TVar x) = inferVar ctx x
inferType ctx (TDef d) = inferDef ctx d
inferType ctx (TData d ps is) = inferData ctx d ps is
inferType ctx (TRec rn pars) = inferRec ctx rn pars
inferType ctx (TDataCon c x) = tcError "non inferrable: can't infer the type of a data constructor"
inferType ctx (TRecCon rec x) = tcError "TODO: infer type of record constructor"
inferType ctx (TLam x te) = tcError "non inferrable: can't infer the type of a lambda"
inferType ctx (TApp u e) = inferApp ctx u e
inferType ctx (TCase d r u bs rt) = inferCase ctx d r u bs rt
inferType ctx (TProj rt projFunc) = tcError "TODO"
  -- inferProj ctx rt projFunc
inferType ctx (TPi x a b) = inferPi ctx x a b
inferType ctx (TSort s) = inferTySort ctx s
inferType ctx (TLet x te te₁) = tcError "non inferrable: can't infer the type of a let"
inferType ctx (TAnn u t) = (_,_) t <$> (TyAnn <$> checkType ctx u t)

{-# COMPILE AGDA2HS inferType #-}

inferSort ctx t = do
  let r = singScope ctx
  st , dt ← inferType ctx t
  s ⟨ rp ⟩ ← reduceToSort r (unType st) "couldn't reduce a term to a sort"
  let cp = CRedL rp CRefl
  return $ s , TyConv dt cp

{-# COMPILE AGDA2HS inferSort #-}
