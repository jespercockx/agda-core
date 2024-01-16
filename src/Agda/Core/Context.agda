open import Scope
open import Agda.Core.GlobalScope

module Agda.Core.Context
  {@0 name    : Set}
  (@0 globals : Globals)
  where

open import Haskell.Extra.Dec
open import Utils.Either
open import Utils.Tactics using (auto)
open import Haskell.Extra.Erase
open import Haskell.Prelude hiding (All; s; t)

open import Agda.Core.Syntax globals
open import Agda.Core.Reduce globals

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

lookupVar : (Γ : Context α) (@0 x : name) (p : x ∈ α) → Type α
lookupVar CtxEmpty x p = inEmptyCase p
lookupVar (CtxExtend Γ y s) x p = raise (rezz _) (inBindCase p
  (λ _ → s)
  (λ q → lookupVar Γ x q))

{-# COMPILE AGDA2HS lookupVar #-}

rezz-scope : (Γ : Context α) → Rezz (Scope name) α
rezz-scope CtxEmpty = rezz _
rezz-scope (CtxExtend Γ x _) =
  rezzCong (λ t → (singleton x) <> t) (rezz-scope Γ)

{-# COMPILE AGDA2HS rezz-scope #-}
