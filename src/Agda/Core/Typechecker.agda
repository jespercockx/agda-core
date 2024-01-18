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
  (tu ⟨ gtu ⟩ ) ← inferType {Γ = Γ} u
  fuel <- tcmFuel
  pifuel <- liftMaybe
              (tryFuel stepEither (Left (makeState tu)) fuel)
              "couldn't construct Fuel for Pi reduction"
  -- FIXME: need to resurrect α, can be done from Γ potentially?
  let rpi = reduce (rezz _) tu pifuel
  (⟨ x ⟩ ( (sv , sr) , (tv , tr))) ← liftEither (getPi rpi)
  let gc = convert {Γ = Γ} (TSort (funSort sv sr)) tu (TPi x sv sr tv tr)
  gtv ← checkType {Γ = Γ} v tv
  -- FIXME: need to resurrect α, can be done from Γ potentially?            
  return ((substTop (rezz _) v tr) ⟨ TyAppE gtu (TyArg gc gtv) ⟩ )
  where
    getPi : Term α
          → Either TCError
                   (Σ0 (name)
                       (λ x → (Sort α × Sort α) × (Type α × Type (x ◃ α))))
    getPi term@(TPi x sa sr at rt) = Right ( ⟨ x ⟩ ((sa , sr) , (at , rt)))
    getPi _ = Left "coudn't reduce the term to become a pi type"
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

checkDef : (@0 f : name)
           (p : f ∈ defScope)
           (ty : Type α)
           → TCM (Γ ⊢ TDef f p ∷ ty)
checkDef f p ty = do
  -- FIXME: doesn't work with the error: weaken subEmpty (lookupAll defType p) != ty
  --return (TyDef f)
  tcError "can't typecheck because idk how"

checkLambda : (@0 x : name)
              (u : Term (x ◃ α))
              (ty : Type α)
              → TCM (Γ ⊢ TLam x u ∷ ty)
checkLambda {Γ = Γ} x u (TPi y su sv tu tv) = do
  -- FIXME: the names x and y don't match
  --d ← checkType {Γ = Γ , x ∶ tu} u tv
  --return (TyLam d)
  tcError "can't typecheck because idk how"
--FIXME
checkLambda x u _ = tcError "can't check lambda against a type that isn't a Pi"

checkLet : (@0 x : name)
           (u : Term α)
           (v : Term (x ◃ α))
           (ty : Type α)
           → TCM (Γ ⊢ TLet x u v ∷ ty)
checkLet {Γ = Γ} x u v ty = do
  tu ⟨ dtu ⟩  ← inferType {Γ = Γ} u
  dtv ← checkType {Γ = Γ , x ∶ tu} v (weaken (subWeaken subRefl) ty)
  -- FIXME: doesn't work with the error: substTop (rezz α) u ty != ty
  --return (TyLet dtu dtv)
  tcError "can't typecheck because idk how"

checkConv : (t : Term α)
            (cty tty : Type α)
          → ∃ (Type α) (λ ty → Γ ⊢ t ∷ ty)
          → TCM (Γ ⊢ t ∷ cty)
checkConv t cty tty (s ⟨ d ⟩) = return (TyConv d (convert tty s cty))

checkType {Γ = Γ} t@(TVar x p) ty = do
  tvar ← inferVar {Γ = Γ} x p
  (tsor ⟨ _ ⟩) ← inferSort {Γ = Γ} ty
  checkConv {Γ = Γ} t ty (TSort tsor) tvar
checkType (TDef f p) ty = checkDef f p ty
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
inferType (TDef d x) = tcError "can't infer the type of a definition"
inferType (TCon c p x) = tcError "not implemented yet"
inferType (TLam x te) = tcError "can't infer the type of a lambda"
inferType (TApp u e) = inferApp u e
inferType (TPi x su sv u v) = inferPi x su sv u v
inferType (TSort s) = inferTySort s
inferType (TLet x te te₁) = tcError "can't infer the type of a let"
inferType (TAnn u t) = tcError "not implemented yet"
