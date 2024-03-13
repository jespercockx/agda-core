open import Haskell.Prelude
  hiding ( All; m; _,_,_)
  renaming (_,_ to infixr 5 _,_)

open import Scope

open import Agda.Core.GlobalScope using (Globals)
import Agda.Core.Signature as Signature

module Agda.Core.Typechecker
    {@0 name    : Set}
    (@0 globals : Globals name)
    (open Signature globals)
    (@0 sig     : Signature)
  where

private open module @0 G = Globals globals

open import Agda.Core.Syntax globals as Syntax
open import Agda.Core.Context globals
open import Agda.Core.Conversion globals sig
open import Agda.Core.Typing globals sig
open import Agda.Core.Reduce globals
open import Agda.Core.Substitute globals
open import Agda.Core.TCM globals sig
open import Agda.Core.Converter globals sig
open import Agda.Core.Utils

open import Haskell.Law.Equality
open import Haskell.Law.Monoid
open import Haskell.Extra.Erase

private variable
  @0 x : name
  @0 α : Scope name

checkCoerce : ∀ Γ (t : Term α)
            → Σ[ ty ∈ Type α ] Γ ⊢ t ∶ ty
            → (cty : Type α)
            → TCM (Γ ⊢ t ∶ cty)
checkCoerce ctx t (gty , dgty) cty =
  TyConv dgty <$> convert ctx (TSort $ typeSort gty) (unType gty) (unType cty)

inferSort : (Γ : Context α) (t : Term α) → TCM (Σ[ s ∈ Sort α ] Γ ⊢ t ∶ sortType s)
inferType : ∀ (Γ : Context α) u → TCM (Σ[ t ∈ Type α ] Γ ⊢ u ∶ t)
checkType : ∀ (Γ : Context α) u (ty : Type α) → TCM (Γ ⊢ u ∶ ty)
checkElim : ∀ (Γ : Context α) u e (ty : Type α) → TCM (Σ[ a ∈ Type α ] TyElim Γ u e ty a)

inferVar : ∀ Γ (@0 x) (p : x ∈ α) → TCM (Σ[ t ∈ Type α ] Γ ⊢ TVar x p ∶ t)
inferVar ctx x p = return $ lookupVar ctx x p , TyTVar p

checkElim ctx u (Syntax.EArg v) ty = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature
  (TPi x at rt) ⟨ rtp ⟩  ← reduceTo r sig (unType ty) fuel
    where _ → tcError "couldn't reduce term to a pi type"

  gtv ← checkType ctx v at
  let sf = piSort (typeSort at) (typeSort rt)
      gc = CRedL rtp CRefl
      tytype = substTopType r v rt
  
  return $ tytype , TyArg gc gtv

checkElim ctx u (Syntax.EProj _ _) ty = tcError "not implemented"
checkElim ctx u (Syntax.ECase bs)  ty = tcError "not implemented"

inferApp : ∀ Γ u e → TCM (Σ[ t ∈ Type α ] Γ ⊢ TApp u e ∶ t)
inferApp ctx u e = do
  let r = rezzScope ctx
  tu , gtu ← inferType ctx u
  a  , gte ← checkElim ctx u e tu 
  return $ a , TyAppE gtu gte

inferPi
  : ∀ Γ (@0 x : name)
  (a : Type α)
  (b : Type (x ◃ α))
  → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TPi x a b ∶ ty)
inferPi ctx x (El su u) (El sv v) = do
  tu <- checkType ctx u (sortType su)
  tv <- checkType (ctx , x ∶ El su u) v (sortType sv)
  let spi = piSort su sv
  return $ sortType spi , TyPi tu tv

inferTySort : ∀ Γ (s : Sort α) → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TSort s ∶ ty)
inferTySort ctx (STyp x) = return $ sortType (sucSort (STyp x)) , TyType

inferDef : ∀ Γ (@0 f : name) (p : f ∈ defScope)
         → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TDef f p ∶ ty)
inferDef ctx f p = do
  rezz sig ← tcmSignature
  return $ weakenType subEmpty (getType sig f p) , TyDef p

checkSubst : ∀ {@0 α β} Γ (t : Telescope α β) (s : β ⇒ α) → TCM (TySubst Γ s t)
checkSubst ctx t SNil = return TyNil
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

checkCon : ∀ Γ
           (@0 c : name)
           (ccs : c ∈ conScope)
           (lc : lookupAll fieldScope ccs ⇒ α)
           (ty : Type α)
         → TCM (Γ ⊢ TCon c ccs lc ∶ ty)
checkCon ctx c ccs lc (El s ty) = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature
  (TDef d dp , els) ⟨ rp ⟩  ← reduceElimView _ _ <$> reduceTo r sig ty fuel
    where
      _ → tcError "can't typecheck a constrctor with a type that isn't a def application"
  (DatatypeDef df) ← return $ getDefinition sig d dp
    where
      _ → tcError "can't convert two constructors when their type isn't a datatype"
  con ← liftMaybe (getConstructor c ccs df)
    "can't find a constructor with such a name"
  params ← liftMaybe (traverse maybeArg els)
    "not all arguments to the datatype are terms"
  psubst ← liftMaybe (listSubst (rezzTel (dataParameterTel df)) params)
    "couldn't construct a substitution for parameters"
  let ctel = substTelescope psubst (conTelescope con)
  tySubst ← checkSubst ctx ctel lc
  let ctype = constructorType d dp c ccs con (substSort psubst (dataSort df)) psubst lc
  checkCoerce ctx (TCon c ccs lc) (ctype , {!TyCon dp df ? ? ? tySubst!}) (El s ty)

checkLambda : ∀ Γ (@0 x : name)
              (u : Term (x ◃ α))
              (ty : Type α)
              → TCM (Γ ⊢ TLam x u ∶ ty)
checkLambda ctx x u (El sp (TPi y tu tv)) =
  TyLam <$> checkType (ctx , x ∶ tu) u (renameTopType (rezzScope ctx) tv)
checkLambda ctx x u (El s ty) = do
  let r = rezzScope ctx
  rezz sig ← tcmSignature
  fuel ← tcmFuel

  (TPi y tu tv) ⟨ rtp ⟩ ← reduceTo r sig ty fuel
    where _ → tcError "couldn't reduce a term to a pi type"
  let gc = CRedR rtp CRefl
      sp = piSort (typeSort tu) (typeSort tv)

  d ← checkType (ctx , x ∶ tu) u (renameTopType (rezzScope ctx) tv)
  return $ TyConv (TyLam {k = sp} d) gc

checkLet : ∀ Γ (@0 x : name)
           (u : Term α)
           (v : Term (x ◃ α))
           (ty : Type α)
           → TCM (Γ ⊢ TLet x u v ∶ ty)
checkLet ctx x u v ty = do
  tu , dtu  ← inferType ctx u
  dtv       ← checkType (ctx , x ∶ tu) v (weakenType (subWeaken subRefl) ty)
  return $ TyLet {r = rezzScope ctx} dtu dtv


checkType ctx (TVar x p) ty = do
  tvar ← inferVar ctx x p
  checkCoerce ctx (TVar x p) tvar ty
checkType ctx (TDef d p) ty = do
  tdef ← inferDef ctx d p
  checkCoerce ctx (TDef d p) tdef ty
checkType ctx (TCon c p x) ty = checkCon ctx c p x ty
checkType ctx (TLam x te) ty = checkLambda ctx x te ty
checkType ctx (TApp u e) ty = do
  tapp ← inferApp ctx u e
  checkCoerce ctx (TApp u e) tapp ty
checkType ctx (TPi x tu tv) ty = do
  tpi ← inferPi ctx x tu tv
  checkCoerce ctx (TPi x tu tv) tpi ty
checkType ctx (TSort s) ty = do
  tts ← inferTySort ctx s
  checkCoerce ctx (TSort s) tts ty
checkType ctx (TLet x u v) ty = checkLet ctx x u v ty
checkType ctx (TAnn u t) ty = tcError "not implemented yet"

{-# COMPILE AGDA2HS checkType #-}

inferType ctx (TVar x p) = inferVar ctx x p
inferType ctx (TDef d p) = inferDef ctx d p
inferType ctx (TCon c p x) = tcError "not implemented yet"
inferType ctx (TLam x te) = tcError "can't infer the type of a lambda"
inferType ctx (TApp u e) = inferApp ctx u e
inferType ctx (TPi x a b) = inferPi ctx x a b
inferType ctx (TSort s) = inferTySort ctx s
inferType ctx (TLet x te te₁) = tcError "can't infer the type of a let"
inferType ctx (TAnn u t) = tcError "not implemented yet"

{-# COMPILE AGDA2HS inferType #-}

inferSort ctx t = do
  let r = rezzScope ctx
  rezz sig ← tcmSignature
  fuel ← tcmFuel
  st , dt ← inferType ctx t
  (TSort s) ⟨ rp ⟩ ← reduceTo r sig (unType st) fuel
    where _ → tcError "couldn't reduce a term to a sort"
  let cp = CRedL rp CRefl
  return $ s , TyConv dt cp

{-# COMPILE AGDA2HS inferSort #-}
