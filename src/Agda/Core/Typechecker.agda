{-# OPTIONS --allow-unsolved-metas #-}
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
open import Agda.Core.Utils

open import Haskell.Law.Equality
open import Haskell.Extra.Erase

private variable
  @0 α : Scope name

postulate
  convert   : (Γ : Context α) (@0 ty : Term α) (@0 a b : Term α) → Γ ⊢ a ≅ b ∶ ty

reduceTo : (_ : Rezz _ α)
           (sig : Signature)
           (v : Term α)
           (_ : Fuel)
         → TCM (∃[ t ∈ Term α ] (ReducesTo sig v t))
reduceTo r sig v f =
  case reduce r sig v f of λ where
    Nothing        → tcError "not enough fuel to reduce a term"
    (Just u) ⦃ p ⦄ → return $ u ⟨ ⟨ r ⟩ f ⟨ p ⟩ ⟩
{-# COMPILE AGDA2HS reduceTo #-}


inferType : ∀ (Γ : Context α) u → TCM (Σ[ t ∈ Term α ] Γ ⊢ u ∶ t)
checkType : ∀ (Γ : Context α) u t (s : Sort α) → TCM (Γ ⊢ u ∶ t)

inferVar : ∀ Γ (@0 x) (p : x ∈ α) → TCM (Σ[ t ∈ Term α ] Γ ⊢ TVar x p ∶ t)
inferVar g x p = return $ unType (lookupVar g x p) , TyTVar p

inferApp : ∀ Γ u e → TCM (Σ[ t ∈ Term α ] Γ ⊢ TApp u e ∶ t)
inferApp ctx u (Syntax.EArg v) = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  tu  , gtu ← inferType ctx u

  (TPi x (El sa at) (El sr rt)) ⟨ rtp ⟩  ← reduceTo r sig tu fuel
    where _ → tcError "couldn't reduce term to a pi type"

  gtv ← checkType ctx v at sa
  let sf = piSort sa sr
      gc = CRedL {t = TSort sf} rtp CRefl

  return $ substTop r v rt , TyAppE gtu (TyArg {k = sf} gc gtv)

inferApp ctx u (Syntax.EProj _ _) = tcError "not implemented"
inferApp ctx u (Syntax.ECase bs)  = tcError "not implemented"

inferPi
  : ∀ Γ (@0 x : name)
  (a : Type α)
  (b : Type (x ◃ α))
  → TCM (Σ[ ty ∈ Term α ] Γ ⊢ TPi x a b ∶ ty)
inferPi ctx x (El su u) (El sv v) = do
  tu <- checkType ctx u (TSort su) (sucSort su)
  tv <- checkType (ctx , x ∶ El su u) v (TSort sv) (sucSort sv)
  pure $ TSort (piSort su sv) , TyPi tu tv

inferTySort : ∀ Γ (s : Sort α) → TCM (Σ[ ty ∈ Term α ] Γ ⊢ TSort s ∶ ty)
inferTySort ctx (STyp x) = return $ TSort (STyp $ 1 + x) , TyType

inferDef : ∀ Γ (@0 f : name) (p : f ∈ defScope) → TCM (Σ[ ty ∈ Term α ] Γ ⊢ TDef f p ∶ ty)
inferDef ctx f p = do
  rezz sig ← tcmSignature
  pure $ weaken subEmpty (unType (getType sig f p)) , TyDef p

checkLambda : ∀ Γ (@0 x : name)
              (u : Term (x ◃ α))
              (ty : Type α)
              → TCM (Γ ⊢ TLam x u ∶ unType ty)
checkLambda ctx x u (El _ (TPi y (El su tu) (El sv tv))) = do
  d ← checkType (ctx , x ∶ El su tu) u (renameTop (rezzScope ctx) tv) {!   !}
  return $ TyLam d
checkLambda ctx x u (El s ty) = do
  let r = rezzScope ctx
  rezz sig ← tcmSignature
  fuel ← tcmFuel

  (TPi y (El su tu) (El sv tv)) ⟨ rtp ⟩ ← reduceTo r sig ty fuel
    where _ → tcError "couldn't reduce a term to a pi type"
  let gc = CRedR {t = TSort s} rtp CRefl

  d ← checkType (ctx , x ∶ El su tu) u (renameTop (rezzScope ctx) tv) {!   !}
  return $ TyConv (TyLam d) gc

checkLet : ∀ Γ (@0 x : name)
           (u : Term α)
           (v : Term (x ◃ α))
           (ty : Type α)
           → TCM (Γ ⊢ TLet x u v ∶ unType ty)
checkLet ctx x u v (El s ty) = do
  tu , dtu  ← inferType ctx u
  dtv       ← checkType (ctx , x ∶ El {!   !} tu) v (weaken (subWeaken subRefl) ty) (weakenSort (subWeaken subRefl) s)
  return $ TyLet {r = rezzScope ctx} dtu dtv

checkCoerce : ∀ Γ (t : Term α)
            → Σ[ ty ∈ Term α ] Γ ⊢ t ∶ ty
            → (cty : Term α) -- the type we want to have
            → (tty : Term α) -- the type of types
            → TCM (Γ ⊢ t ∶ cty)
--FIXME: first reduce the type, patmatch on the type
--the depending on what the type is do either
--for vars
--for defs
--for cons
--for labmda
--for app
--for pi
--for sort
--the rest should be reduced away
checkCoerce ctx t (s , d) cty tty = do
  return $ TyConv d (convert ctx tty s cty)

checkType ctx t@(TVar x p) ty s = do
  tvar ← inferVar ctx x p
  checkCoerce ctx t tvar ty (TSort s)
checkType ctx (TDef d p) ty s =  do
  tdef ← inferDef ctx d p
  checkCoerce ctx (TDef d p) tdef ty (TSort s)
checkType ctx (TCon c p x) ty s = tcError "not implemented yet"
checkType ctx (TLam x te) ty s = checkLambda ctx x te (El s ty)
checkType ctx t@(TApp u e) ty s = do
  tapp ← inferApp ctx u e
  checkCoerce ctx t tapp ty (TSort s)
checkType ctx t@(TPi x (El su u) (El sv v)) ty s = do
  tpi ← inferPi ctx x (El su u) (El sv v)
  checkCoerce ctx t tpi ty (TSort s)
checkType ctx t@(TSort s) ty st = do
  tts ← inferTySort ctx s
  checkCoerce ctx t tts ty (TSort s)
checkType ctx (TLet x u v) ty s = checkLet ctx x u v (El s ty)
checkType ctx (TAnn u t) ty s = tcError "not implemented yet"

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

inferSort : (Γ : Context α) (t : Term α) → TCM (Σ[ s ∈ Sort α ] Γ ⊢ t ∶ TSort s)
inferSort ctx t = do
  let r = rezzScope ctx
  rezz sig ← tcmSignature
  fuel ← tcmFuel
  st , dt ← inferType ctx t
  (TSort s) ⟨ rp ⟩ ← reduceTo r sig st fuel
    where _ → tcError "couldn't reduce a term to a sort"
  let cp = CRedL {t = TSort $ sucSort s} rp CRefl
  return $ s , TyConv dt cp

{-# COMPILE AGDA2HS inferSort #-}
