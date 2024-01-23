open import Scope

open import Agda.Core.GlobalScope using (Globals)
import Agda.Core.Signature as Signature

open import Haskell.Prelude hiding (All; a; b; c; e; s; t; m)

module Agda.Core.Typing
    {@0 name    : Set}
    (@0 globals : Globals name)
    (open Signature globals)
    (@0 sig     : Signature)
  where

private open module @0 G = Globals globals

open import Haskell.Extra.Erase
open import Haskell.Extra.Loop

open import Utils.Tactics using (auto)

open import Agda.Core.Syntax globals
open import Agda.Core.Reduce globals
open import Agda.Core.Conversion globals sig
open import Agda.Core.Context globals
open import Agda.Core.Substitute globals

private variable
  @0 x y     : name
  @0 α       : Scope name
  @0 s t u v : Term α
  @0 a b c   : Type α
  @0 k l m   : Sort α
  @0 n       : Nat
  @0 e       : Elim α

data TyTerm (@0 Γ : Context α) : @0 Term α → @0 Type α → Set

-- TyElim Γ e t f means: if  Γ ⊢ u : t  then  Γ ⊢ appE u [ e ] : f (appE u)
data TyElim  (@0 Γ : Context α) : @0 Elim α → @0 Type α → @0 ((Elim α → Term α) → Type α) → Set

infix 3 TyTerm
syntax TyTerm Γ u t = Γ ⊢ u ∶ t

data TyTerm {α} Γ where

  TyTVar
    : (@0 p : x ∈ α)
    ----------------------------------
    → Γ ⊢ TVar x p ∶ lookupVar Γ x p

  TyDef
    : {@0 f : name} (@0 p : f ∈ defScope)
    ----------------------------------------------
    → Γ ⊢ TDef f p ∶ weakenType subEmpty (getType sig f p)

  -- TODO: constructor typing

  TyLam
    : {@0 r : Rezz _ α}
    → Γ , x ∶ a ⊢ u ∶ renameTopType r b
    -------------------------------
    → Γ ⊢ TLam x u ∶ El k (TPi y a b)

  TyAppE
    : Γ ⊢ u ∶ a
    → TyElim Γ e a (λ _ → b)
    ------------------------------------
    → Γ ⊢ TApp u e ∶ b

  TyPi
    : Γ ⊢ u ∶ sortType k
    → Γ , x ∶ (El k u) ⊢ v ∶ sortType l
    ----------------------------------------------------------
    → Γ ⊢ TPi x (El k u) (El l v) ∶ sortType (piSort k l)

  TyType
    -------------------------------------------
    : Γ ⊢ TSort k ∶ sortType (sucSort k)

  TyLet
    : {@0 r : Rezz _ α}
    → Γ ⊢ u ∶ a
    → Γ , x ∶ a ⊢ v ∶ weakenType (subWeaken subRefl) b
    ----------------------------------------------
    → Γ ⊢ TLet x u v ∶ b

  TyAnn
    : Γ ⊢ u ∶ a
    ------------------
    → Γ ⊢ TAnn u a ∶ sortType (typeSort a)

  TyConv
    : Γ ⊢ u ∶ a
    → Γ ⊢ (unType a) ≅ (unType b) ∶ (unType c)
    ----------------
    → Γ ⊢ u ∶ b

{-# COMPILE AGDA2HS TyTerm #-}

data TyElim {α} Γ where
    TyArg : {@0 r : Rezz _ α}
        → Γ ⊢ (unType c) ≅ TPi x a b ∶ TSort k
        → Γ ⊢ u ∶ a
        → TyElim Γ (EArg u) c (λ h → substTopType r u b)
    -- TODO: proj
    -- TODO: case

{-# COMPILE AGDA2HS TyElim #-}

{-
-- TyElims Γ es f t₁ t₂ means: if  Γ ⊢ h [] : t₁  then  Γ ⊢ h es : t₂
data TyElims Γ where
    TyDone : ∀ {@0 u} → TyElims Γ [] u t t
    TyMore : ∀ {@0 h f}
        → TyElim  Γ e        s             f
        → TyElims Γ es       (h ∘ (e ∷_)) (f h) t
        → TyElims Γ (e ∷ es) h             s    t

{-# COMPILE AGDA2HS TyElims #-}
-}
