
open import Scope.Core
open import Scope.Split
open import Scope.Sub
open import Scope.In
open import Scope.All

open import Utils.Dec
open import Utils.Either
open import Utils.Erase

open import Haskell.Prelude hiding (All; t)

import Syntax
import Reduce

module Context
  {@0 name  : Set}
  (@0 defs     : Scope name)
  (@0 cons     : Scope name)
  (   conArity : All (λ _ → Scope name) cons)
  (   defType  : All (λ _ → Syntax.Type defs cons conArity mempty) defs)
  where

open Syntax defs cons conArity
open Reduce defs cons conArity

private variable
  @0 x     : name
  @0 α β γ : Scope name
  @0 t u v w : Term α
  @0 ts us vs ws : Elims α

data Context : Scope name → Set where
    CxEmpty : Context mempty
    CxVar   : Context α → (x : name) → Type α → Context (x ◃ α)

syntax CxVar Γ x t = Γ , x ∶ t

data TyVar : (Γ : Context α) (@0 x : name) → x ∈ α → Type α → Set where
    TVHere  : ∀ {@0 α} {Γ : Context α} {t : Type α}
         → TyVar (Γ , x ∶ t) x inHere (raise (rezz _) t)
    TVThere : ∀ {@0 α} {@0 x y : name} {Γ : Context α} {p : x ∈ α} {t u : Type α}
         → TyVar Γ x p t → TyVar (Γ , y ∶ u) x (inThere p) (raise (rezz _) t)
