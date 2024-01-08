
-- open import Utils
-- open Variables
open import Scope
import Syntax
import Reduce
open import Haskell.Extra.Erase
open import Utils.Tactics using (auto)
open import Haskell.Prelude hiding (All)
open import Haskell.Extra.Loop

module Typing
    {@0 name  : Set}
    (defs     : Scope name)
    (cons     : Scope name)
    (conArity : All (λ _ → Scope name) cons)
    (defType  : All (λ _ → Syntax.Type defs cons conArity mempty) defs)
  where

open Syntax defs cons conArity
open Reduce defs cons conArity
open import Substitute {name} defs cons conArity

private
  variable @0 α : Scope name
           @0 x : name

data Context : Scope name → Set where
    []    : Context mempty
    _,_∶_ : Context α → (@0 x : name) → Type α → Context (x ◃ α)

infix 4 _,_∶_

data TyVar : (Γ : Context α) (@0 x : name) → x ∈ α → Type α → Set where
    zero : ∀ {@0 α} {Γ : Context α} {t : Type α} 
         → TyVar (Γ , x ∶ t) x inHere (raise (rezz [ x ]) t)
    suc  : ∀ {@0 α} {@0 x y : name} {Γ : Context α} {p : x ∈ α} {t u : Type α}
         → TyVar Γ x p t → TyVar (Γ , y ∶ u) x (inThere p) (raise (rezz [ y ]) t)

_⊢var_∷_ : (Γ : Context α) (@0 x : name) → {@(tactic auto) _ : x ∈ α} → Type α → Set
_⊢var_∷_ Γ x {p} t = TyVar Γ x p t

data _⊢_∷_ (Γ : Context α) : Term α → Type α → Set

-- TyElim Γ e t f means:
--   if  Γ ⊢ u : t  then  Γ ⊢ appE u [ e ] : f (appE u)
data TyElim  (Γ : Context α) : Elim α → Type α → ((Elims α → Term α) → Type α) → Set
-- TyElims Γ es f t₁ t₂ means:
--   if  Γ ⊢ h [] : t₁  then  Γ ⊢ h es : t₂
data TyElims (Γ : Context α) : Elims α → (Elims α → Term α) → Type α → Type α → Set

data _⊢_∷_ {α} Γ where

    var : ∀ {t} {p : x ∈ α}

        → TyVar Γ x p t
        -------------------
        → Γ ⊢ TVar x p ∷ t

    def : ∀ {f} {p : f ∈ defs}

        -------------------------------------------------
        → Γ ⊢ TDef f p ∷ (weaken subEmpty (defType ! f))

    -- TODO: constructor typing
    lam : ∀ {u} {t₁} {t₂}

        → (Γ , x ∶ t₁) ⊢ u ∷ t₂
        ----------------------------------------
        → Γ            ⊢ TLam x u ∷ TPi x t₁ t₂

    appE : ∀ {u es t₁ t₂} → Γ ⊢ u ∷ t₁ → TyElims Γ es (applyElims u) t₁ t₂ → Γ ⊢ applyElims u es ∷ t₂

    pi : ∀ {la lb x a b}

       → Γ           ⊢ a ∷ TSort (STyp la)
       → (Γ , x ∶ a) ⊢ b ∷ (TSort (STyp lb))
       -----------------------------------------------------
       → Γ           ⊢ TPi x a b ∷ TSort (STyp (max la lb))

    type : ∀ {l}

         --------------------------------------------
         → Γ ⊢ TSort (STyp l) ∷ TSort (STyp (suc l))

    -- TODO: more general PTS rules
    let′ : ∀ {x u v t₁ t₂}

         → Γ            ⊢ u ∷ t₁
         → (Γ , x ∶ t₁) ⊢ v ∷ t₂
         ------------------------------------------
         → Γ ⊢ TLet x u v ∷ substTop (rezz α) u t₂

data TyElim Γ where
    arg : ∀ {@0 n} {t x a b u}
          (f : Fuel stepEither (Left (makeState t)))
        → reduce n t f ≡ TPi x a b
        → TyElim Γ (EArg u) t (λ h → substTop (rezz _) u b)
    -- TODO: proj
    -- TODO: case

data TyElims Γ where
    [] : ∀ {u t} → TyElims Γ [] u t t
    _∷_ : ∀ {e es h t₁ t₂ f}
        → TyElim  Γ e        t₁            f
        → TyElims Γ es       (h ∘ (e ∷_)) (f h) t₂
        → TyElims Γ (e ∷ es) h             t₁   t₂
