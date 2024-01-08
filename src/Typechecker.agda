open import Scope
import Syntax
import Reduce
import Typing
import Context
import Conversion
open import Haskell.Extra.Erase
open import Haskell.Prelude hiding (All)
-- TODO remove
open import Agda.Builtin.Sigma

module Typechecker
    {@0 name  : Set}
    (defs     : Scope name)
    (cons     : Scope name)
    (conArity : All (λ _ → Scope name) cons)
    (defType  : All (λ _ → Syntax.Type defs cons conArity mempty) defs)
  where

open Syntax defs cons conArity
open Typing defs cons conArity defType
open Context defs cons conArity
open Conversion defs cons conArity defType

private
  variable @0 α : Scope name
           Γ : Context α

postulate
  convert : (ty : Type α) (a b : Term α)
          → Conv {α = α} Γ ty a b

-- FIXME
-- for now returning a sigma, not sure what's supposed to be here
inferType : (te : Term α) → Maybe (Σ (Type α) (λ ty → Γ ⊢ te ∷ ty))

checkType : (te : Term α) (ty : Type α) → Γ ⊢ te ∷ ty

inferVar : (@0 x : name)
           (p : x ∈ α)
           → Σ (Type α) (λ t → Γ ⊢ TVar x p ∷ t)
inferVar = {!!}

inferApp : (u : Term α)
           (e : Elim α)
           → Σ (Type α) (λ ty → Γ ⊢ TApp u e ∷ ty)
inferApp = {!!}

inferApps : (u : Term α)
            (es : Elims α)
          → Σ (Type α) (λ ty → Γ ⊢ applyElims u es ∷ ty)
inferApps = {!!}

inferPi : (@0 x : name)
          (u : Term α)
          (v : Term (x ◃ α))
          → Σ (Type α) (λ ty → Γ ⊢ TPi x u v ∷ ty)
inferPi = {!!}

inferSort : (s : Sort α)
            → Σ (Type α) (λ ty → Γ ⊢ TSort s ∷ ty)
inferSort = {!!}

checkDef : (@0 f : name)
           (p : f ∈ defs)
           (ty : Type α)
           → Γ ⊢ TDef f p ∷ ty
checkDef = {!!}

checkLambda : (@0 x : name)
              (u : Term (x ◃ α))
              (ty : Type α)
              → Γ ⊢ TLam x u ∷ ty
checkLambda = {!!}

checkLet : (@0 x : name)
           (u : Term α)
           (v : Term (x ◃ α))
           (ty : Type α)
           → Γ ⊢ TLet x u v ∷ ty
checkLet = {!!}

checkConv : (t : Term α)
            (cty tty : Type α)
          → Σ (Type α) (λ ty → Γ ⊢ t ∷ ty)
          → Γ ⊢ t ∷ cty
checkConv t cty tty sd = TyConv (snd sd) (convert tty (fst sd) cty)

checkType t@(TVar x p) ty =  checkConv t ty {!!} (inferVar x p)
checkType (TDef f p) ty = checkDef f p ty
checkType (TCon c p x) ty = {!!}
checkType (TLam x te) ty =  checkLambda x te ty
checkType t@(TApp u e) ty = checkConv t ty {!!} (inferApp u e)
checkType t@(TPi x u v) ty =  checkConv t ty {!!} (inferPi x u v)
checkType t@(TSort s) ty = checkConv t ty {!!} (inferSort s)
checkType (TLet x te te₁) ty = checkLet x te te₁ ty

inferType (TVar x p) = Just (inferVar x p)
inferType (TDef d x) = Nothing
inferType (TCon c p x) = Nothing
inferType (TLam x te) = Nothing
inferType (TApp u e) = Just (inferApp u e)
inferType (TPi x u v) = Just (inferPi x u v)
inferType (TSort s) = Just (inferSort s)
inferType (TLet x te te₁) = Nothing
