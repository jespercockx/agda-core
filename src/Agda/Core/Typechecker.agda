open import Haskell.Prelude
  hiding ( All; m; _,_,_)
  renaming (_,_ to infixr 5 _,_)

open import Scope
open import Utils.Tactics using (auto)

open import Agda.Core.GlobalScope using (Globals; Name)
open import Agda.Core.Signature
open import Agda.Core.Syntax as Syntax
open import Agda.Core.Context
open import Agda.Core.Conversion
open import Agda.Core.Typing
open import Agda.Core.Reduce
open import Agda.Core.Substitute
open import Agda.Core.TCM
open import Agda.Core.TCMInstances
open import Agda.Core.Converter
open import Agda.Core.Utils

open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Haskell.Law.Equality
open import Haskell.Law.Monoid

module Agda.Core.Typechecker
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x : Name
  @0 α : Scope Name

checkCoerce : ∀ Γ (t : Term α)
            → Σ[ ty ∈ Type α ] Γ ⊢ t ∶ ty
            → (cty : Type α)
            → TCM (Γ ⊢ t ∶ cty)
checkCoerce ctx t (gty , dgty) cty = do
  let r = rezzScope ctx
  TyConv dgty <$> convert r (unType gty) (unType cty)
{-# COMPILE AGDA2HS checkCoerce #-}

tcmGetType : (@0 x : Name) {@(tactic auto) xp : x ∈ defScope} → TCM (Rezz (getType sig x))
tcmGetType x = do
  rsig ← tcmSignature
  return (rezzCong (λ sig → getType sig x) rsig)
{-# COMPILE AGDA2HS tcmGetType #-}

tcmGetDefinition : (@0 x : Name) {@(tactic auto) xp : x ∈ defScope} → TCM (Rezz (getDefinition sig x))
tcmGetDefinition x = do
  rsig ← tcmSignature
  return (rezzCong (λ sig → getDefinition sig x) rsig)
{-# COMPILE AGDA2HS tcmGetDefinition #-}

inferVar : ∀ Γ (@0 x) {@(tactic auto) p : x ∈ α} → TCM (Σ[ t ∈ Type α ] Γ ⊢ TVar x ∶ t)
inferVar ctx x = return $ lookupVar ctx x , TyTVar x
{-# COMPILE AGDA2HS inferVar #-}

inferSort : (Γ : Context α) (t : Term α) → TCM (Σ[ s ∈ Sort α ] Γ ⊢ t ∶ sortType s)
inferType : ∀ (Γ : Context α) u → TCM (Σ[ t ∈ Type α ] Γ ⊢ u ∶ t)
checkType : ∀ (Γ : Context α) u (ty : Type α) → TCM (Γ ⊢ u ∶ ty)
checkBranches : ∀ {@0 cons : Scope Name}
                  (Γ : Context α)
                  (rz : Rezz cons)
                  (bs : Branches α cons)
                  (dt : Datatype) (ps : dataParameterScope dt ⇒ α)
                  (rt : Type (x ◃ α))
                → TCM (TyBranches Γ dt ps rt bs)

inferApp : ∀ Γ u v → TCM (Σ[ t ∈ Type α ] Γ ⊢ TApp u v ∶ t)
inferApp ctx u v = do
  let r = rezzScope ctx
  tu , gtu ← inferType ctx u
  (TPi x at rt) ⟨ rtp ⟩  ← reduceTo r (unType tu)
    where _ → tcError "couldn't reduce term to a pi type"
  gtv ← checkType ctx v at
  let sf = piSort (typeSort at) (typeSort rt)
      gc = CRedL rtp CRefl
      tytype = substTopType r v rt
  return (tytype , TyApp gtu gc gtv)
{-# COMPILE AGDA2HS inferApp #-}

inferCase : ∀ {@0 cs} Γ u bs rt → TCM (Σ[ t ∈ Type α ] Γ ⊢ TCase {cs = cs} {x = x} u bs rt ∶ t)
inferCase ctx u bs rt = do
  let r = rezzScope ctx
  El s tu , gtu ← inferType ctx u
  (TDef d , params) ⟨ rp ⟩  ← reduceAppView _ <$> reduceTo r tu
    where
      _ → tcError "can't typecheck a constrctor with a type that isn't a def application"
  DatatypeDef df ⟨ dep ⟩ ← tcmGetDefinition d
    where
      _ → tcError "can't convert two constructors when their type isn't a datatype"
  (psubst , ixs) ← liftMaybe (listSubst (rezzTel (dataParameterTel df)) params)
    "couldn't construct a substitution for parameters"
  (isubst , loargs) ← liftMaybe (listSubst (rezzTel (dataIndexTel df)) ixs)
    "couldn't construct a substitution for indexes"
  assert (null loargs)
    "there are more arguments to the datatype then parameters and indices"
  (Erased refl) ← liftMaybe
    (allInScope {γ = conScope} (allBranches bs) (mapAll fst $ dataConstructors df))
    "couldn't verify that branches cover all constructors"
  cb ← checkBranches ctx (rezzBranches bs) bs df psubst rt
  let ds = substSort psubst (dataSort df)
  cc ← convert r tu (unType $ dataType d ds psubst isubst)
  return (substTopType r u rt , TyCase {k = ds} d df dep {is = isubst} bs rt gtu cc cb)

{-# COMPILE AGDA2HS inferCase #-}

inferPi
  : ∀ Γ (@0 x : Name)
  (a : Type α)
  (b : Type (x ◃ α))
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

inferDef : ∀ Γ (@0 f : Name) {@(tactic auto) p : f ∈ defScope}
         → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TDef f ∶ ty)
inferDef ctx f = do
  ty ⟨ eq ⟩ ← tcmGetType f
  return $ weakenType subEmpty ty , subst0 (λ ty → TyTerm ctx (TDef f) (weakenType subEmpty ty)) eq (TyDef f)
{-# COMPILE AGDA2HS inferDef #-}

checkSubst : ∀ {@0 α β} Γ (t : Telescope α β) (s : β ⇒ α) → TCM (TySubst Γ s t)
checkSubst ctx t SNil =
  caseTelEmpty t λ where ⦃ refl ⦄ → return TyNil
checkSubst ctx t (SCons x s) =
  caseTelBind t λ where ty rest ⦃ refl ⦄ → do
    tyx ← checkType ctx x ty
    let
      r = rezzScope ctx
      sstel = subst0 (λ (@0 β) → Subst β β)
                (IsLawfulMonoid.rightIdentity iLawfulMonoidScope _)
                (concatSubst (subToSubst r (subJoinHere _ subRefl)) SNil)
      stel = substTelescope (SCons x sstel) rest
    tyrest ← checkSubst ctx stel s
    return (TyCons tyx tyrest)
{-# COMPILE AGDA2HS checkSubst #-}

checkBranch : ∀ {@0 con : Name} (Γ : Context α)
                (bs : Branch α con)
                (dt : Datatype)
                (ps : dataParameterScope dt ⇒ α)
                (rt : Type (x ◃ α))
            → TCM (TyBranch Γ dt ps rt bs)
checkBranch ctx (BBranch c r rhs) dt ps rt = do
  let ra = rezzScope ctx
  cid ⟨ refl ⟩  ← liftMaybe (getConstructor c dt)
    "can't find a constructor with such a name"
  let (c∈conScope , con) = lookupAll (dataConstructors dt) cid
      ctel = substTelescope ps (conTelescope con)
      cargs = weakenSubst (subJoinHere (rezzCong revScope r) subRefl)
                          (revIdSubst r)
      idsubst = weakenSubst (subJoinDrop (rezzCong revScope r) subRefl)
                            (idSubst ra)
      bsubst = SCons (TCon c {c∈conScope} cargs) idsubst
  crhs ← checkType (addContextTel ctel ctx) rhs (substType bsubst rt)
  return (TyBBranch c cid {rα = ra} rhs crhs)
{-# COMPILE AGDA2HS checkBranch #-}

checkBranches ctx (rezz cons) bs dt ps rt =
  caseScope cons
    (λ where {{refl}} → caseBsNil bs (λ where {{refl}} → return TyBsNil))
    (λ ch ct → λ where
      {{refl}} → caseBsCons bs (λ bh bt → λ where
        {{refl}} → TyBsCons <$> checkBranch ctx bh dt ps rt
                            <*> checkBranches ctx (rezzBranches bt) bt dt ps rt))
{-# COMPILE AGDA2HS checkBranches #-}

checkCon : ∀ Γ
           (@0 c : Name)
           {@(tactic auto) ccs : c ∈ conScope}
           (cargs : lookupAll fieldScope ccs ⇒ α)
           (ty : Type α)
         → TCM (Γ ⊢ TCon c cargs ∶ ty)
checkCon ctx c {ccs} cargs (El s ty) = do
  let r = rezzScope ctx
  (TDef d , params) ⟨ rp ⟩  ← reduceAppView _ <$> reduceTo r ty
    where
      _ → tcError "can't typecheck a constrctor with a type that isn't a def application"
  DatatypeDef df ⟨ dep ⟩ ← tcmGetDefinition d
    where
      _ → tcError "can't convert two constructors when their type isn't a datatype"
  cid ⟨ refl ⟩  ← liftMaybe (getConstructor c df)
    "can't find a constructor with such a name"
  (psubst , ixs) ← liftMaybe (listSubst (rezzTel (dataParameterTel df)) params)
    "couldn't construct a substitution for parameters"
  (isubst , loargs) ← liftMaybe (listSubst (rezzTel (dataIndexTel df)) ixs)
    "couldn't construct a substitution for indexes"
  assert (null loargs)
    "there are more arguments to the datatype then parameters and indices"
  let con = snd (lookupAll (dataConstructors df) cid)
      ctel = substTelescope psubst (conTelescope con)
      ctype = constructorType d c {ccs} con (substSort psubst (dataSort df)) psubst cargs
  tySubst ← checkSubst ctx ctel cargs
  checkCoerce ctx (TCon c {ccs} cargs) (ctype , TyCon d c dep tySubst) (El s ty)
{-# COMPILE AGDA2HS checkCon #-}

checkLambda : ∀ Γ (@0 x : Name)
              (u : Term (x ◃ α))
              (ty : Type α)
              → TCM (Γ ⊢ TLam x u ∶ ty)
checkLambda ctx x u (El sp (TPi y tu tv)) =
  TyLam <$> checkType (ctx , x ∶ tu) u (renameTopType (rezzScope ctx) tv)
checkLambda ctx x u (El s ty) = do
  let r = rezzScope ctx

  (TPi y tu tv) ⟨ rtp ⟩ ← reduceTo r ty
    where _ → tcError "couldn't reduce a term to a pi type"
  let gc = CRedR rtp CRefl
      sp = piSort (typeSort tu) (typeSort tv)

  d ← checkType (ctx , x ∶ tu) u (renameTopType (rezzScope ctx) tv)
  return $ TyConv (TyLam {k = sp} d) gc
{-# COMPILE AGDA2HS checkLambda #-}

checkLet : ∀ Γ (@0 x : Name)
           (u : Term α)
           (v : Term (x ◃ α))
           (ty : Type α)
           → TCM (Γ ⊢ TLet x u v ∶ ty)
checkLet ctx x u v ty = do
  tu , dtu  ← inferType ctx u
  dtv       ← checkType (ctx , x ∶ tu) v (weakenType (subWeaken subRefl) ty)
  return $ TyLet {r = rezzScope ctx} dtu dtv
{-# COMPILE AGDA2HS checkLet #-}


checkType ctx (TVar x) ty = do
  tvar ← inferVar ctx x
  checkCoerce ctx (TVar x) tvar ty
checkType ctx (TDef d) ty = do
  tdef ← inferDef ctx d
  checkCoerce ctx (TDef d) tdef ty
checkType ctx (TCon c x) ty = checkCon ctx c x ty
checkType ctx (TLam x te) ty = checkLambda ctx x te ty
checkType ctx (TApp u e) ty = do
  tapp ← inferApp ctx u e
  checkCoerce ctx (TApp u e) tapp ty
checkType ctx (TCase {cs = cs} u bs rt) ty = do
  tapp ← inferCase {cs = cs} ctx u bs rt
  checkCoerce ctx (TCase u bs rt) tapp ty
checkType ctx (TProj u f) ty = tcError "not implemented: projections"
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
inferType ctx (TCon c x) = tcError "non inferrable: can't infer the type of a constructor"
inferType ctx (TLam x te) = tcError "non inferrable: can't infer the type of a lambda"
inferType ctx (TApp u e) = inferApp ctx u e
inferType ctx (TCase u bs rt) = inferCase ctx u bs rt
inferType ctx (TProj u f) = tcError "not implemented: projections"
inferType ctx (TPi x a b) = inferPi ctx x a b
inferType ctx (TSort s) = inferTySort ctx s
inferType ctx (TLet x te te₁) = tcError "non inferrable: can't infer the type of a let"
inferType ctx (TAnn u t) = (_,_) t <$> TyAnn <$> checkType ctx u t

{-# COMPILE AGDA2HS inferType #-}

inferSort ctx t = do
  let r = rezzScope ctx
  st , dt ← inferType ctx t
  (TSort s) ⟨ rp ⟩ ← reduceTo r (unType st)
    where _ → tcError "couldn't reduce a term to a sort"
  let cp = CRedL rp CRefl
  return $ s , TyConv dt cp

{-# COMPILE AGDA2HS inferSort #-}
