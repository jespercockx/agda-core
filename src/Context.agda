
open import Scope.Core
open import Scope.Split
open import Scope.Sub
open import Scope.In
open import Scope.All

open import Haskell.Extra.Dec
open import Utils.Either
open import Utils.Tactics using (auto)
open import Haskell.Extra.Erase

open import Haskell.Prelude hiding (All; s; t)

import Syntax
import Reduce

module Context
  {@0 name  : Set}
  (@0 defs     : Scope name)
  (@0 cons     : Scope name)
  (@0 conArity : All (λ _ → Scope name) cons)
  where

open Syntax defs cons conArity
open Reduce defs cons conArity

private variable
  @0 x y : name
  @0 α : Scope name
  @0 s t u v : Term α

data Context : @0 Scope name → Set where
  CtxEmpty  : Context mempty
  CtxExtend : Context α → (@0 x : name) → Type α → Context (x ◃ α)

{-# COMPILE AGDA2HS Context #-}

_,_∶_ : Context α → (@0 x : name) → Type α → Context (x ◃ α)
_,_∶_ = CtxExtend

infix 4 _,_∶_

{-# COMPILE AGDA2HS _,_∶_ inline #-}

private variable
  @0 Γ : Context α

data TyVar : (@0 Γ : Context α) (@0 x : name) → @0 x ∈ α → @0 Type α → Set where

  TyHere  : TyVar (Γ , x ∶ t) x inHere (raise (rezz [ x ]) t)

  TyThere : ∀ {@0 p : x ∈ α}

        → TyVar Γ x p t
        --------------------------------------------------------
        → TyVar (Γ , y ∶ u) x (inThere p) (raise (rezz [ y ]) t)

{-# COMPILE AGDA2HS TyVar #-}

_⊢var_∷_ : (Γ : Context α) (@0 x : name) → {@(tactic auto) _ : x ∈ α} → Type α → Set
_⊢var_∷_ Γ x {p} t = TyVar Γ x p t

{-# COMPILE AGDA2HS _⊢var_∷_ inline #-}
