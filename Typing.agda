
open import Utils
open Variables
import Scope
import Syntax
import Reduce

module Typing
    {Name : Set} (let open Scope Name)
    (defs : Scope)
    (cons     : Scope)
    (conArity : All (λ _ → Scope) cons)
    (defType : All (λ _ → Syntax.Type defs cons conArity ∅) defs)
  where

open Syntax defs cons conArity
open Reduce defs cons conArity

data Context : Scope → Set where
    []    : Context ∅
    _,_∶_ : Context α → (x : Name) → Type α → Context (x ◃ α)

infix 4 _,_∶_

data TyVar : (Γ : Context α) (@0 x : Name) → x ∈ α → Type α → Set where
    zero : ∀ {@0 α} {Γ : Context α} {t : Type α} 
         → TyVar (Γ , x ∶ t) x here (raise t)
    suc  : ∀ {@0 α} {@0 x y : Name} {Γ : Context α} {p : x ∈ α} {t u : Type α}
         → TyVar Γ x p t → TyVar (Γ , y ∶ u) x (there p) (raise t)

_⊢var_∷_ : (Γ : Context α) (@0 x : Name) → {@(tactic auto) _ : x ∈ α} → Type α → Set
_⊢var_∷_ Γ x {p} t = TyVar Γ x p t

data _⊢_∷_ (Γ : Context α) : Term α → Type α → Set

-- TyElim Γ e t f means:
--   if  Γ ⊢ u : t  then  Γ ⊢ appE u [ e ] : f (appE u)
data TyElim  (Γ : Context α) : Elim α → Type α → ((Elims α → Term α) → Type α) → Set
-- TyElims Γ es f t₁ t₂ means:
--   if  Γ ⊢ h [] : t₁  then  Γ ⊢ h es : t₂
data TyElims (Γ : Context α) : Elims α → (Elims α → Term α) → Type α → Type α → Set

data _⊢_∷_ {α} Γ where
    var : ∀ {t} {p : x ∈ α} → TyVar Γ x p t → Γ ⊢ var x ∷ t
    def : ∀ {f} {p : f ∈ defs} → Γ ⊢ def f {p} ∷ (weaken ⊆-∅ (defType ! f))
    -- TODO: constructor typing
    lam : ∀ {u} {t₁} {t₂} → (Γ , x ∶ t₁) ⊢ u ∷ t₂ → Γ ⊢ lam x u ∷ pi x t₁ t₂
    appE : ∀ {u es t₁ t₂} → Γ ⊢ u ∷ t₁ → TyElims Γ es (appE u) t₁ t₂ → Γ ⊢ appE u es ∷ t₂
    pi : ∀ {la lb x a b} → Γ ⊢ a ∷ sort (type la) → (Γ , x ∶ a) ⊢ b ∷ (sort (type lb)) → Γ ⊢ pi x a b ∷ sort (type (la Nat.⊔ lb))
    type : ∀ {l} → Γ ⊢ sort (type l) ∷ sort (type (suc l))
    -- TODO: more general PTS rules
    let′ : ∀ {x u v t₁ t₂} → Γ ⊢ u ∷ t₁ → (Γ , x ∶ t₁) ⊢ v ∷ t₂ → Γ ⊢ let′ x u v ∷ substTop u t₂

data TyElim Γ where
    arg : ∀ {@0 n} {t x a b u} → reduce n t ≡ just (pi x a b) → TyElim Γ (arg u) t (λ h → substTop u b)
    -- TODO: proj
    -- TODO: case

data TyElims Γ where
    [] : ∀ {u t} → TyElims Γ [] u t t
    _∷_ : ∀ {e es h t₁ t₂ f}
        → TyElim  Γ e        t₁            f
        → TyElims Γ es       (h ∘ (e ∷_)) (f h) t₂
        → TyElims Γ (e ∷ es) h             t₁   t₂