{-# OPTIONS --allow-unsolved-metas #-}
open import Haskell.Prelude hiding ( All; m )
open import Scope
open import GlobalScope

import Agda.Core.Syntax as Syntax

module Agda.Core.Typechecker
    {@0 name    : Set}
    (@0 globals : Globals)
    (defType    : All (λ _ → Syntax.Type globals (mempty {{iMonoidScope}})) (Globals.defScope globals))
  where

open Syntax globals
open import Agda.Core.Context globals
open import Agda.Core.Conversion globals defType
open import Agda.Core.Typing globals defType
open import Agda.Core.Reduce globals
open import Agda.Core.Substitute globals

open import Haskell.Prim.Functor
open import Haskell.Prim.Applicative
open import Haskell.Control.Monad
open import Haskell.Extra.Erase
open import Haskell.Extra.Loop


private
  variable @0 α : Scope name
           Γ : Context α

module Exists where
  open import Agda.Primitive
  private variable
    ℓ ℓ′ : Level
  
  record ∃ (a : Set ℓ) (P : (@0 _ : a) → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
    constructor _⟨_⟩
    field
      value : a
      proof : P value
  open ∃ public
  {-# COMPILE AGDA2HS ∃ unboxed #-}

open Exists


record TCM (a : Set) : Set where
  constructor mkTCM
  field
    runTCM : Nat → Either String a

tcmFuel : TCM Nat
tcmFuel = mkTCM (λ f → Right f)

TCError = String

postulate instance
  iFunctorTCM : Functor TCM
  iApplicativeTCM : Applicative TCM
  iMonadTCM : Monad TCM

postulate
  inferSort : (t : Type α)
            → TCM (∃ (Sort α) (λ s → Γ ⊢ t ∷ TSort s))
  convert : (@0 ty : Type α) (@0 a b : Term α)
          → Conv {α = α} Γ ty a b
  tcError : TCError -> TCM a
  liftMaybe : Maybe a → TCError → TCM a
  liftEither : Either TCError a → TCM a

-- this is Either and not TCM because otherwise some meta doesn't get solved 🤷
getPi : (t : Term α)
      → Either TCError
               (Σ0 (name)
                   (λ x → ∃ ((Sort α × Sort α) × (Type α × Type (x ◃ α)))
                             (λ ( (sa , sb) , (ta , tb) ) → t ≡ TPi x sa sb ta tb)
                    ))
getPi term@(TPi x sa sr at rt) = Right ( ⟨ x ⟩ ((sa , sr) , (at , rt)) ⟨ refl ⟩)
getPi _ = Left "coudn't reduce the term to become a pi type"

{-# TERMINATING #-}
inferType : (te : Term α)
          → TCM (∃ (Type α) (λ ty → Γ ⊢ te ∷ ty))

checkType : (te : Term α) (ty : Type α)
          → TCM (Γ ⊢ te ∷ ty)

inferVar : (@0 x : name)
           (p : x ∈ α)
           → TCM (∃ (Type α) (λ t → Γ ⊢ TVar x p ∷ t))
inferVar {Γ = Γ} x p = return ( (lookupVar Γ x p) ⟨ TyTVar ⟩)

inferApp : (u : Term α)
           (e : Elim α)
           → TCM (∃ (Type α) (λ ty → Γ ⊢ TApp u e ∷ ty))
inferApp {α = α} {Γ = Γ} u (Syntax.EArg v) = do
  let r = (rezz-scope Γ)
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

inferPi : (@0 x : name)
          (su sv : Sort α)
          (u : Term α)
          (v : Term (x ◃ α))
          → TCM (∃ (Type α) (λ ty → Γ ⊢ TPi x su sv u v ∷ ty))
inferPi {Γ = Γ} x su sv u v = do
  tu <- checkType {Γ = Γ} u (TSort su)
  tv <- checkType {Γ = Γ , x ∶ u} v (TSort (weakenSort (subWeaken subRefl) sv))
  return ( (TSort (funSort su sv)) ⟨ TyPi tu tv ⟩ )

inferTySort : (s : Sort α)
            → TCM (∃ (Type α) (λ ty → Γ ⊢ TSort s ∷ ty))
inferTySort (STyp x) = return (TSort (STyp (suc x)) ⟨ TyType ⟩)

inferDef : (@0 f : name)
           (p : f ∈ defs)
         → TCM (∃ (Type α) (λ ty → Γ ⊢ TDef f p ∷ ty))
inferDef f p = return (((weaken subEmpty (defType ! f))) ⟨ (TyDef f) ⟩)

checkLambda : (@0 x : name)
              (u : Term (x ◃ α))
              (ty : Type α)
              → TCM (Γ ⊢ TLam x u ∷ ty)
checkLambda {Γ = Γ} x u (TPi y su sv tu tv) = do
  d ← checkType {Γ = Γ , y ∶ tu} (renameTop (rezz-scope Γ) u) tv
  return (TyLam d)
--FIXME: reduce ty and see if it's a Pi
checkLambda x u _ = tcError "can't check lambda against a type that isn't a Pi"

checkLet : (@0 x : name)
           (u : Term α)
           (v : Term (x ◃ α))
           (ty : Type α)
           → TCM (Γ ⊢ TLet x u v ∷ ty)
checkLet {Γ = Γ} x u v ty = do
  tu ⟨ dtu ⟩  ← inferType {Γ = Γ} u
  dtv ← checkType {Γ = Γ , x ∶ tu} v (weaken (subWeaken subRefl) ty)
  return (TyLet {r = rezz-scope Γ} dtu dtv)

checkConv : (t : Term α)
            (cty tty : Type α)
          → ∃ (Type α) (λ ty → Γ ⊢ t ∷ ty)
          → TCM (Γ ⊢ t ∷ cty)
checkConv t cty tty (s ⟨ d ⟩) = return (TyConv d (convert tty s cty))

checkType {Γ = Γ} t@(TVar x p) ty = do
  tvar ← inferVar {Γ = Γ} x p
  (tsor ⟨ _ ⟩) ← inferSort {Γ = Γ} ty
  checkConv {Γ = Γ} t ty (TSort tsor) tvar
checkType {Γ = Γ} (TDef d p) ty =  do
  tdef ← inferDef d p
  (tsor ⟨ _ ⟩) ← inferSort {Γ = Γ} ty
  checkConv {Γ = Γ} (TDef d p) ty (TSort tsor) tdef
checkType (TCon c p x) ty = tcError "not implemented yet"
checkType (TLam x te) ty =  checkLambda x te ty
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
