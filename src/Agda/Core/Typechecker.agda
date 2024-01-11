{-# OPTIONS --allow-unsolved-metas #-}
open import Haskell.Prelude hiding (All)
open import Scope
open import GlobalScope

import Agda.Core.Syntax as Syntax

module Agda.Core.Typechecker
    {@0 name    : Set}
    (@0 globals : Globals)
    (defType    : All (λ _ → Syntax.Type globals (mempty {{iMonoidScope}})) (Globals.defScope globals))
  where

open import Haskell.Extra.Erase

open Syntax globals
open import Agda.Core.Context globals
open import Agda.Core.Conversion globals defType
open import Agda.Core.Typing globals defType

private
  variable @0 α : Scope name
           Γ : Context α

postulate
  convert : (@0 ty : Type α) (@0 a b : Term α)
          → Conv {α = α} Γ ty a b

record TCM (a : Set) : Set where
  constructor mkTCM
  field
    runTCM : Either String a

TCError = String

postulate instance
  iFunctorTCM : Functor TCM
  iApplicativeTCM : Applicative TCM
  iMonadTCM : Monad TCM

postulate
  tcError : TCError -> TCM a

inferType : (te : Term α)
          → TCM (Σ0 (Type α) (λ ty → Γ ⊢ te ∷ ty))

checkType : (te : Term α) (ty : Type α)
          → TCM (Γ ⊢ te ∷ ty)

inferVar : (@0 x : name)
           (p : x ∈ α)
           → TCM (Σ0 (Type α) (λ t → Γ ⊢ TVar x p ∷ t))
inferVar {Γ = Γ} x p = return (⟨ lookupVar Γ x p ⟩ TyTVar)

inferApp : (u : Term α)
           (e : Elim α)
           → TCM (Σ0 (Type α) (λ ty → Γ ⊢ TApp u e ∷ ty))
inferApp u e = {!!}

inferApps : (u : Term α)
            (es : Elims α)
          → TCM (Σ0 (Type α) (λ ty → Γ ⊢ applyElims u es ∷ ty))
inferApps = {!!}

inferPi : (@0 x : name)
          (su sv : Sort α)
          (u : Term α)
          (v : Term (x ◃ α))
          → TCM (Σ0 (Type α) (λ ty → Γ ⊢ TPi x su sv u v ∷ ty))
inferPi = {!!}

inferTySort : (s : Sort α)
            → TCM (Σ0 (Type α) (λ ty → Γ ⊢ TSort s ∷ ty))
inferTySort = {!!}

checkDef : (@0 f : name)
           (p : f ∈ defScope)
           (ty : Type α)
           → TCM (Γ ⊢ TDef f p ∷ ty)
checkDef = {!!}

checkLambda : (@0 x : name)
              (u : Term (x ◃ α))
              (ty : Type α)
              → TCM (Γ ⊢ TLam x u ∷ ty)
checkLambda = {!!}

checkLet : (@0 x : name)
           (u : Term α)
           (v : Term (x ◃ α))
           (ty : Type α)
           → TCM (Γ ⊢ TLet x u v ∷ ty)
checkLet = {!!}

checkConv : (t : Term α)
            (cty tty : Type α)
          → Σ0 (Type α) (λ ty → Γ ⊢ t ∷ ty)
          → TCM (Γ ⊢ t ∷ cty)
checkConv t cty tty (⟨ s ⟩ d) = return (TyConv d (convert tty s cty))

inferSort : (t : Term α)
          → TCM (Σ0 (Sort α) (λ s → Γ ⊢ t ∷ TSort s))
inferSort t = {!!}

checkType t@(TVar x p) ty = checkConv t ty {!!} =<< inferVar x p
checkType (TDef f p) ty = checkDef f p ty
checkType (TCon c p x) ty = {!!}
checkType (TLam x te) ty =  checkLambda x te ty
checkType t@(TApp u e) ty = checkConv t ty {!!} =<< (inferApp u e)
checkType t@(TPi x su sv u v) ty =  checkConv t ty {!!} =<< (inferPi x su sv u v)
checkType t@(TSort s) ty = checkConv t ty {!!} =<< (inferTySort s)
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
