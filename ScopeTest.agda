
open import Utils
import Scope

module ScopeTest (Name : Set) where

open Scope Name
open Variables

data Term (@0 α : Scope) : Set where
  var : (x : Name) → {{α ≡ [ x ]}} → Term α
  lam : (y : Name) → Term (y ◃ α) → Term α
  app : {{α₁ ⋈ α₂ ≡ α}} → Term α₁ → Term α₂ → Term α

postulate
  i j k : Name

var! : (x : Name) → Term [ x ]
var! x = var x

opaque
  unfolding [_]

  myterm : Term ∅
  myterm = lam i (lam j (app {{⋈-comm ⋈-refl}} (var i ) (var! j)))

  test = {! myterm !}
