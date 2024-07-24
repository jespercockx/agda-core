module Agda.Core.GlobalScope where

open import Scope
open import Utils.Tactics using (auto)
open import Haskell.Prelude hiding (All; s; t)

Name = String

record Globals : Set where
  field
    defScope     : Scope Name
    dataScope    : Scope Name
    dataParScope : (@0 d : Name) → {@(tactic auto) _ : d ∈ dataScope} → Scope Name
    dataIxScope  : (@0 d : Name) → {@(tactic auto) _ : d ∈ dataScope} → Scope Name
    conScope     : Scope Name
    fieldScope   : (@0 c : Name) → {@(tactic auto) _ : c ∈ conScope} → Scope Name
open Globals public
{-# COMPILE AGDA2HS Globals #-}

