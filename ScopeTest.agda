
open import Utils
open import Scope

module ScopeTest (Name : Set) (s : IScope Name) where

open IScope s

data Term (@0 α : Scope) : Set where
  var : (x : Name) → {{Singleton x α}} → Term α
  lam : (y : Name) → Term (y ◃ α) → Term α
  app : {{α₁ ⋈ α₂ ≡ α}} → Term α₁ → Term α₂ → Term α

postulate
  i j k : Name

var! : (x : Name) → Term [ x ]
var! x = var x {{[]-singleton}}

myterm : Term ∅
myterm = lam i (lam j (app {{⋈-comm ⋈-refl}} (var i {{left-singleton []-singleton ∅-empty}}) (var! j)))
