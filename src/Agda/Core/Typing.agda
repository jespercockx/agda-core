open import Scope
open import GlobalScope

import Agda.Core.Syntax as Syntax

open import Haskell.Prelude hiding (All; e; s; t; m)

module Agda.Core.Typing
    {@0 name    : Set}
    (@0 globals : Globals)
    (@0 defType : All (λ _ → Syntax.Type globals (mempty {{iMonoidScope}})) (Globals.defScope globals))
  where

open import Haskell.Extra.Erase
open import Haskell.Extra.Loop

open import Utils.Tactics using (auto)

open Syntax globals
open import Agda.Core.Reduce globals
open import Agda.Core.Conversion globals defType
open import Agda.Core.Context globals
open import Agda.Core.Substitute globals

private variable
  @0 x y : name
  @0 α : Scope name
  @0 s t u v : Term α
  @0 k l m : Sort α
  @0 n : Nat
  @0 e : Elim α

data TyTerm (@0 Γ : Context α) : @0 Term α → @0 Type α → Set

_⊢_∷_ : (Γ : Context α) → Term α → Type α → Set
Γ ⊢ u ∷ a = TyTerm Γ u a

{-# COMPILE AGDA2HS _⊢_∷_ inline #-}

-- TyElim Γ e t f means:
--   if  Γ ⊢ u : t  then  Γ ⊢ appE u [ e ] : f (appE u)
data TyElim  (@0 Γ : Context α) : @0 Elim α → @0 Type α → @0 ((Elim α → Term α) → Type α) → Set

{-
-- TyElims Γ es f t₁ t₂ means:
--   if  Γ ⊢ h [] : t₁  then  Γ ⊢ h es : t₂
data TyElims (@0 Γ : Context α) : @0 Elims α → @0 (Elims α → Term α) → @0 Type α → @0 Type α → Set
-}

data TyTerm {α} Γ where

    TyTVar : {@0 p : x ∈ α}
        -------------------
        → Γ ⊢ TVar x p ∷ (lookupVar Γ x p)

    TyDef : (@0 f : name) {@0 p : f ∈ defScope}

        -------------------------------------------------
        → Γ ⊢ TDef f p ∷ (weaken subEmpty (defType ! f))
    -- TODO: constructor typing

    TyLam :

         (Γ , x ∶ s) ⊢ u ∷ t
       ------------------------------------------------------------
       →  Γ          ⊢ TLam x u ∷ TPi x k l s t

    TyAppE :
          Γ ⊢ u ∷ s
        → TyElim Γ e s ( λ _ → t )
        ------------------------------------
        → Γ ⊢ TApp u e ∷ t

    TyPi :

         Γ           ⊢ s ∷ TSort k
       → (Γ , x ∶ s) ⊢ t ∷ TSort (weakenSort (subWeaken subRefl) l)
       -----------------------------------------------------
       → Γ           ⊢ TPi x k l s t ∷ TSort (funSort k l)

    TyType :

        --------------------------------------------
         Γ ⊢ TSort (STyp n) ∷ TSort (STyp (suc n))

    TyLet :

           Γ           ⊢ u ∷ s
         → (Γ , x ∶ s) ⊢ v ∷ t
         ------------------------------------------
         → Γ ⊢ TLet x u v ∷ substTop (rezz α) u t

    TyAnn :
            Γ ⊢ u ∷ t
         -------------------
          → Γ ⊢ TAnn u t ∷ t

    TyConv :

           Γ ⊢ u ∷ t
         → Conv Γ s t v
         -------------------------------
         → Γ ⊢ u ∷ v

{-# COMPILE AGDA2HS TyTerm #-}

data TyElim Γ where
    TyArg :
          Conv Γ (TSort k) v (TPi x l m s t)
        → TyTerm Γ u s
        → TyElim Γ (EArg u) v (λ h → substTop (rezz _) u t)
    -- TODO: proj
    -- TODO: case

{-# COMPILE AGDA2HS TyElim #-}

{-
data TyElims Γ where
    TyDone : ∀ {@0 u} → TyElims Γ [] u t t
    TyMore : ∀ {@0 h f}
        → TyElim  Γ e        s             f
        → TyElims Γ es       (h ∘ (e ∷_)) (f h) t
        → TyElims Γ (e ∷ es) h             s    t

{-# COMPILE AGDA2HS TyElims #-}
-}
