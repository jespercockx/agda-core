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
  inferSort : (Γ : Context α) (t : Type α) → TCM (Σ[ s ∈ Sort α ] Γ ⊢ t ∶ TSort s)
  convert   : (Γ : Context α) (@0 ty : Type α) (@0 a b : Term α) → Γ ⊢ a ≅ b ∶ ty

inferType : ∀ (Γ : Context α) u → TCM (Σ[ t ∈ Type α ] Γ ⊢ u ∶ t)
checkType : ∀ (Γ : Context α) u t → TCM (Γ ⊢ u ∶ t)


inferVar : ∀ Γ (@0 x) (p : x ∈ α) → TCM (Σ[ t ∈ Type α ] Γ ⊢ TVar x p ∶ t)
inferVar g x p = return (lookupVar g x p , TyTVar p)

inferApp : ∀ Γ u e → TCM (Σ[ t ∈ Type α ] Γ ⊢ TApp u e ∶ t)
inferApp ctx u (Syntax.EArg v) = do
  let r = rezzScope ctx

  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  tu  , gtu ← inferType ctx u
  stu , _   ← inferSort ctx tu

  case reduce r sig tu fuel of λ where
    Nothing → tcError "not enough fuel to reduce term"
    (Just (TPi x sa sr at rt)) ⦃ p ⦄ → do
      gtv ← checkType ctx v at
      let gc = CRedL (⟨ r ⟩ fuel ⟨ p ⟩) CRefl
      pure $ substTop r v rt , TyAppE gtu (TyArg {k = funSort sa sr} gc gtv)
    (Just _) → tcError "couldn't reduce term to pi type"

inferApp ctx u (Syntax.EProj _ _) = tcError "not implemented"
inferApp ctx u (Syntax.ECase bs)  = tcError "not implemented"

inferPi
  : ∀ Γ (@0 x : name)
  (su sv : Sort α)
  (u : Term α)
  (v : Term (x ◃ α))
  → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TPi x su sv u v ∶ ty)
inferPi ctx x su sv u v = do
  tu <- checkType ctx u (TSort su)
  tv <- checkType (ctx , x ∶ u) v (TSort (weakenSort (subWeaken subRefl) sv))
  pure $ TSort (funSort su sv) , TyPi tu tv

inferTySort : ∀ Γ (s : Sort α) → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TSort s ∶ ty)
inferTySort ctx (STyp x) = pure $ TSort (STyp (suc x)) , TyType

inferDef : ∀ Γ (@0 f : name) (p : f ∈ defScope) → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TDef f p ∶ ty)
inferDef ctx f p = do
  rezz sig ← tcmSignature
  pure $ weaken subEmpty (getType sig f p) , TyDef p

checkLambda : ∀ Γ (@0 x : name)
              (u : Term (x ◃ α))
              (ty : Type α)
              → TCM (Γ ⊢ TLam x u ∶ ty)
checkLambda ctx x u (TPi y su sv tu tv) = do
  d ← checkType (ctx , x ∶ tu) u (renameTop (rezzScope ctx) tv)
  return (TyLam d)
--FIXME: reduce ty and see if it's a Pi
checkLambda ctx x u _ = tcError "can't check lambda against a type that isn't a Pi"

checkLet : ∀ Γ (@0 x : name)
           (u : Term α)
           (v : Term (x ◃ α))
           (ty : Type α)
           → TCM (Γ ⊢ TLet x u v ∶ ty)
checkLet ctx x u v ty = do
  tu , dtu  ← inferType ctx u
  dtv       ← checkType (ctx , x ∶ tu) v (weaken (subWeaken subRefl) ty)

  return (TyLet {r = rezzScope ctx} dtu dtv)

checkCoerce : ∀ Γ (t : Term α)
            → Σ[ ty ∈ Type α ] Γ ⊢ t ∶ ty
            → (cty : Type α) -- the type we want to have
            → (tty : Type α) -- the type of types
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
checkCoerce ctx t (s , d) cty tty = return (TyConv d (convert ctx tty s cty))



checkType ctx (TVar x p) ty = do
  tvar     ← inferVar ctx x p
  tsor , _ ← inferSort ctx ty
  checkCoerce ctx (TVar x p) tvar ty (TSort tsor)
checkType ctx (TDef d p) ty =  do
  tdef     ← inferDef ctx d p
  tsor , _ ← inferSort ctx ty
  checkCoerce ctx (TDef d p) tdef ty (TSort tsor)
checkType ctx (TCon c p x) ty = tcError "not implemented yet"
checkType ctx (TLam x te) ty =  checkLambda ctx x te ty
checkType ctx (TApp u e) ty = do
  tapp     ← inferApp ctx u e
  tsor , _ ← inferSort ctx ty
  checkCoerce ctx (TApp u e) tapp ty (TSort tsor)
checkType ctx (TPi x su sv u v) ty = do
  tpi      ← inferPi ctx x su sv u v
  tsor , _ ← inferSort ctx ty
  checkCoerce ctx (TPi x su sv u v) tpi ty (TSort tsor)
checkType ctx (TSort s) ty = do
  tts      ← inferTySort ctx s
  tsor , _ ← inferSort ctx ty
  checkCoerce ctx (TSort s) tts ty (TSort tsor)
checkType ctx (TLet x u v) ty = checkLet ctx x u v ty
checkType ctx (TAnn u t) ty = tcError "not implemented yet"

{-# COMPILE AGDA2HS checkType #-}

inferType ctx (TVar x p) = inferVar ctx x p
inferType ctx (TDef d p) = inferDef ctx d p
inferType ctx (TCon c p x) = tcError "not implemented yet"
inferType ctx (TLam x te) = tcError "can't infer the type of a lambda"
inferType ctx (TApp u e) = inferApp ctx u e
inferType ctx (TPi x su sv u v) = inferPi ctx x su sv u v
inferType ctx (TSort s) = inferTySort ctx s
inferType ctx (TLet x te te₁) = tcError "can't infer the type of a let"
inferType ctx (TAnn u t) = tcError "not implemented yet"

{-# COMPILE AGDA2HS inferType #-}
