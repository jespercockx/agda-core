{-# OPTIONS --allow-unsolved-metas #-}
open import Scope

import Syntax
import Reduce
import Typing
import Context
import Conversion
import Substitute

open import Haskell.Prelude hiding ( All; m )
open import Haskell.Prim.Functor
open import Haskell.Prim.Applicative
open import Haskell.Control.Monad
open import Haskell.Extra.Erase
open import Haskell.Extra.Loop

module Typechecker
    {@0 name  : Set}
  where

-- NOTE(flupe): agda2hs doesn't support non-erased module parameters for now
postulate
  defs     : Scope name
  cons     : Scope name
  conArity : All (λ _ → Scope name) cons
  defType  : All (λ _ → Syntax.Type defs cons conArity mempty) defs

open Syntax defs cons conArity
open Typing defs cons conArity defType
open Context defs cons conArity
open Reduce defs cons conArity
open Conversion defs cons conArity defType
open Substitute defs cons conArity
open import Agda.Core.Utils

private variable
  @0 α : Scope name
  Γ    : Context α
  m    : Set → Set

TCError = String
{-# COMPILE AGDA2HS TCError #-}

record TCM (a : Set) : Set where
  constructor MkTCM
  field
    runTCM : Nat → Either TCError a
open TCM public
{-# COMPILE AGDA2HS TCM #-}

postulate instance
  iFunctorTCM     : Functor TCM
  iApplicativeTCM : Applicative TCM
  iMonadTCM       : Monad TCM


tcError : TCError -> TCM a
tcError e = MkTCM (const (Left e))
{-# COMPILE AGDA2HS tcError #-}

liftEither : Either TCError a → TCM a
liftEither e = MkTCM (const e)
{-# COMPILE AGDA2HS liftEither #-}

liftMaybe : Maybe a → TCError → TCM a
liftMaybe Nothing  e = tcError e
liftMaybe (Just x) e = pure x
{-# COMPILE AGDA2HS liftMaybe #-}

tcmFuel : TCM Nat
tcmFuel = MkTCM Right
{-# COMPILE AGDA2HS tcmFuel #-}

postulate
  inferSort : (t : Type α) → TCM (∃[ s ] Γ ⊢ t ∷ TSort s)
  convert   : (@0 ty : Type α) (@0 a b : Term α) → Γ ⊢ a ≅ b ∶ ty

-- this is Either and not TCM because otherwise some meta doesn't get solved 🤷
getPi
  : (t : Term α)
  → Either TCError
           (Σ0 (name)
               (λ x → Σ[ ((sa , sb) , (ta , tb)) ∈ ((Sort α × Sort α) × (Type α × Type (x ◃ α))) ] (t ≡ TPi x sa sb ta tb)
                ))
getPi term@(TPi x sa sr at rt) = Right ( ⟨ x ⟩ ((sa , sr) , (at , rt)) ⟨ refl ⟩)
getPi _ = Left "coudn't reduce the term to become a pi type"
{-# COMPILE AGDA2HS getPi #-}

{-# TERMINATING #-}
inferType : (x : Term α) → TCM (∃[ ty ] Γ ⊢ x ∷ ty)
checkType : (x : Term α) (ty : Type α) → TCM (Γ ⊢ x ∷ ty)

{-# COMPILE AGDA2HS inferType #-}
{-# COMPILE AGDA2HS checkType #-}

inferVar : (@0 x : name) (p : x ∈ α) → TCM (∃[ t ] Γ ⊢ TVar x p ∷ t)
inferVar {Γ = Γ} x p = return ( (lookupVar Γ x p) ⟨ TyTVar ⟩)

{-# COMPILE AGDA2HS inferVar #-}

inferApp : (u : Term α) (e : Elim α)
         → TCM (∃[ ty ] Γ ⊢ TApp u e ∷ ty)
inferApp {α = α} {Γ = Γ} u (Syntax.EArg v) = do
  let r = (rezzScope Γ)
  (tu ⟨ gtu ⟩ ) ← inferType {Γ = Γ} u
  fuel <- tcmFuel
  pifuel <- liftMaybe
              (tryFuel stepEither (Left (makeState tu)) fuel)
              "couldn't construct Fuel for Pi reduction"
  let rpi = reduce r tu pifuel
  --Would be nice to have an inlined case here instead of getPi
  --https://agda.readthedocs.io/en/latest/language/syntactic-sugar.html#do-notation
  --but it won't get compiled to haskell
  (⟨ x ⟩ ((sv , sr) , (tv , tr)) ⟨ eq ⟩) ← liftEither (getPi rpi)
  --FIXME: this should be CRedL, but that requires eq to be matched with refl
  --atm agda can't unify it
  let gc = convert {Γ = Γ} (TSort (funSort sv sr)) tu (TPi x sv sr tv tr)
  gtv ← checkType {Γ = Γ} v tv
  return ((substTop r v tr) ⟨ TyAppE gtu (TyArg gc gtv) ⟩ )
inferApp {Γ = Γ} u (Syntax.EProj x x₁) = tcError "not implemented"
inferApp {Γ = Γ} u (Syntax.ECase bs) = tcError "not implemented"
{-# COMPILE AGDA2HS inferApp #-}

inferPi
  : (@0 x : name) (su sv : Sort α)
    (u : Term α)
    (v : Term (x ◃ α))
  → TCM (∃[ ty ] Γ ⊢ TPi x su sv u v ∷ ty)
inferPi {Γ = Γ} x su sv u v = do
  tu <- checkType u (TSort su)
  tv <- checkType v (TSort (weakenSort (subWeaken subRefl) sv))
  return ((TSort (funSort su sv)) ⟨ TyPi tu tv ⟩)
{-# COMPILE AGDA2HS inferPi #-}

inferTySort
  : (s : Sort α)
  → TCM (∃[ ty ] Γ ⊢ TSort s ∷ ty)
inferTySort (STyp x) = return (TSort (STyp (suc x)) ⟨ TyType ⟩)
{-# COMPILE AGDA2HS inferTySort #-}

inferDef
  : (@0 f : name) (p : f ∈ defs)
  → TCM (∃[ ty ] Γ ⊢ TDef f p ∷ ty)
inferDef f p = return (((weaken subEmpty (defType ! f))) ⟨ (TyDef f) ⟩)
{-# COMPILE AGDA2HS inferDef #-}

checkLambda : (@0 x : name)
              (u : Term (x ◃ α))
              (ty : Type α)
              → TCM (Γ ⊢ TLam x u ∷ ty)
checkLambda {Γ = Γ} x u (TPi y su sv tu tv) = do
  d ← checkType {Γ = Γ , y ∶ tu} (renameTop (rezzScope Γ) u) tv
  return (TyLam d)
--FIXME: reduce ty and see if it's a Pi
checkLambda x u _ = tcError "can't check lambda against a type that isn't a Pi"
{-# COMPILE AGDA2HS checkLambda #-}

checkLet : (@0 x : name)
           (u : Term α)
           (v : Term (x ◃ α))
           (ty : Type α)
           → TCM (Γ ⊢ TLet x u v ∷ ty)
checkLet {Γ = Γ} x u v ty = do
  tu ⟨ dtu ⟩  ← inferType {Γ = Γ} u
  dtv ← checkType {Γ = Γ , x ∶ tu} v (weaken (subWeaken subRefl) ty)
  return (TyLet dtu dtv)
{-# COMPILE AGDA2HS checkLet #-}

checkConv : (t : Term α)
            (cty tty : Type α)
          → ∃[ ty ] Γ ⊢ t ∷ ty
          → TCM (Γ ⊢ t ∷ cty)
checkConv t cty tty (s ⟨ d ⟩) = return (TyConv d (convert tty s cty))
{-# COMPILE AGDA2HS checkConv #-}

checkType {Γ = Γ} t@(TVar x p) ty = do
  tvar ← inferVar {Γ = Γ} x p
  (tsor ⟨ _ ⟩) ← inferSort {Γ = Γ} ty
  checkConv {Γ = Γ} t ty (TSort tsor) tvar

checkType {Γ = Γ} (TDef d p) ty =  do
  tdef ← inferDef d p
  (tsor ⟨ _ ⟩) ← inferSort {Γ = Γ} ty
  checkConv {Γ = Γ} (TDef d p) ty (TSort tsor) tdef

checkType (TCon c p x) ty = tcError "not implemented yet"

checkType (TLam x te) ty = checkLambda x te ty

checkType {Γ = Γ} t@(TApp u e) ty = do
  tapp ← inferApp {Γ = Γ} u e
  (tsor ⟨ _ ⟩) ← inferSort {Γ = Γ} ty
  checkConv {Γ = Γ} t ty (TSort tsor) tapp

checkType {Γ = Γ} t@(TPi x su sv u v) ty = do
  tpi ← inferPi {Γ = Γ} x su sv u v
  (tsor ⟨ _ ⟩) ← inferSort {Γ = Γ} ty
  checkConv {Γ = Γ} t ty (TSort tsor) tpi

checkType {Γ = Γ} t@(TSort s) ty = do
  tts ← inferTySort {Γ = Γ} s
  (tsor ⟨ _ ⟩) ← inferSort {Γ = Γ} ty
  checkConv {Γ = Γ} t ty (TSort tsor) tts
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
