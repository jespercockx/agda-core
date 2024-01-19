{-# OPTIONS --allow-unsolved-metas #-}
open import Haskell.Prelude
  hiding ( All; m; _,_,_)
  renaming (_,_ to infixr 5 _,_)

open import Scope

open import Agda.Core.GlobalScope using (Globals)
import Agda.Core.Signature

module Agda.Core.Typechecker
    {@0 name    : Set}
    (@0 globals : Globals name)
    (open Agda.Core.Signature globals)
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
  Γ    : Context α
           
postulate
  inferSort : (t : Type α) → TCM (Σ[ s ∈ Sort α ] Γ ⊢ t ∶ TSort s)
  convert : (@0 ty : Type α) (@0 a b : Term α) → Γ ⊢ a ≅ b ∶ ty

inferType : ∀ u   → TCM (Σ[ t ∈ Type α ] Γ ⊢ u ∶ t)
{-# COMPILE AGDA2HS inferType #-}

checkType : ∀ u t → TCM (Γ ⊢ u ∶ t)
{-# COMPILE AGDA2HS checkType #-}

inferVar : ∀ (@0 x) (p : x ∈ α) → TCM (Σ[ t ∈ Type α ] Γ ⊢ TVar x p ∶ t)
inferVar {Γ = g} x p = return (lookupVar g x p , TyTVar p)

inferApp : ∀ u e → TCM (Σ[ t ∈ Type α ] Γ ⊢ TApp u e ∶ t)
inferApp {Γ = Γ} u (Syntax.EArg v) = do
  let r = rezzScope Γ

  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  tu  , gtu ← inferType {Γ = Γ} u
  stu , _   ← inferSort {Γ = Γ} tu

  case reduce r sig tu fuel of λ where
    Nothing → tcError "not enough fuel to reduce term"
    (Just (TPi x sa sr at rt)) ⦃ p ⦄ → do
      gtv ← checkType {Γ = Γ} v at
      let gc = CRedL (⟨ r ⟩ fuel ⟨ p ⟩) CRefl
      pure $ substTop r v rt , TyAppE gtu (TyArg {k = funSort sa sr} gc gtv)
    (Just _) → tcError "couldn't reduce term to pi type"

inferApp {Γ = Γ} u (Syntax.EProj x x₁) = tcError "not implemented"
inferApp {Γ = Γ} u (Syntax.ECase bs) = tcError "not implemented"

inferPi : (@0 x : name)
          (su sv : Sort α)
          (u : Term α)
          (v : Term (x ◃ α))
          → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TPi x su sv u v ∶ ty)
inferPi {Γ = Γ} x su sv u v = do
  tu <- checkType {Γ = Γ} u (TSort su)
  tv <- checkType {Γ = Γ , x ∶ u} v (TSort (weakenSort (subWeaken subRefl) sv))
  pure $ TSort (funSort su sv) , TyPi tu tv

inferTySort : (s : Sort α) → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TSort s ∶ ty)
inferTySort (STyp x) = pure $ TSort (STyp (suc x)) , TyType

inferDef : (@0 f : name) (p : f ∈ defScope ) → TCM (Σ[ ty ∈ Type α ] Γ ⊢ TDef f p ∶ ty)
inferDef f p = do
  rezz sig ← tcmSignature
  pure $ weaken subEmpty (getType sig f p) , TyDef p

checkLambda : (@0 x : name)
              (u : Term (x ◃ α))
              (ty : Type α)
              → TCM (Γ ⊢ TLam x u ∶ ty)
checkLambda {Γ = Γ} x u (TPi y su sv tu tv) = do
  d ← checkType {Γ = Γ , x ∶ tu} u (renameTop (rezzScope Γ) tv)
  return (TyLam d)
--FIXME: reduce ty and see if it's a Pi
checkLambda x u _ = tcError "can't check lambda against a type that isn't a Pi"

checkLet : (@0 x : name)
           (u : Term α)
           (v : Term (x ◃ α))
           (ty : Type α)
           → TCM (Γ ⊢ TLet x u v ∶ ty)
checkLet {Γ = Γ} x u v ty = do
  tu , dtu  ← inferType {Γ = Γ} u
  dtv ← checkType {Γ = Γ , x ∶ tu} v (weaken (subWeaken subRefl) ty)
  return (TyLet {r = rezzScope Γ} dtu dtv)

checkCoerce : (t : Term α)
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
checkCoerce t (s , d) cty tty = return (TyConv d (convert tty s cty))



checkType {Γ = Γ} t@(TVar x p) ty = do
  tvar     ← inferVar {Γ = Γ} x p
  tsor , _ ← inferSort {Γ = Γ} ty
  checkCoerce {Γ = Γ} t tvar ty (TSort tsor)
checkType {Γ = Γ} (TDef d p) ty =  do
  tdef     ← inferDef d p
  tsor , _ ← inferSort {Γ = Γ} ty
  checkCoerce {Γ = Γ} (TDef d p) tdef ty (TSort tsor)
checkType (TCon c p x) ty = tcError "not implemented yet"
checkType (TLam x te) ty =  checkLambda x te ty
checkType {Γ = Γ} t@(TApp u e) ty = do
  tapp     ← inferApp {Γ = Γ} u e
  tsor , _ ← inferSort {Γ = Γ} ty
  checkCoerce {Γ = Γ} t tapp ty (TSort tsor)
checkType {Γ = Γ} t@(TPi x su sv u v) ty = do
  tpi      ← inferPi {Γ = Γ} x su sv u v
  tsor , _ ← inferSort {Γ = Γ} ty
  checkCoerce {Γ = Γ} t tpi ty (TSort tsor)
checkType {Γ = Γ} t@(TSort s) ty = do
  tts      ← inferTySort {Γ = Γ} s
  tsor , _ ← inferSort {Γ = Γ} ty
  checkCoerce {Γ = Γ} t tts ty (TSort tsor)
checkType (TLet x u v) ty = checkLet x u v ty
checkType (TAnn u t) ty = tcError "not implemented yet"

inferType (TVar x p) = inferVar x p
inferType (TDef d p) = inferDef d p
inferType (TCon c p x) = tcError "not implemented yet"
inferType (TLam x te) = tcError "can't infer the type of a lambda"
inferType (TApp u e) = inferApp u e
inferType (TPi x su sv u v) = inferPi x su sv u v
inferType (TSort s) = inferTySort s
inferType (TLet x te te₁) = tcError "can't infer the type of a let"
inferType (TAnn u t) = tcError "not implemented yet"

