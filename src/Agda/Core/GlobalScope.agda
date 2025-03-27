module Agda.Core.GlobalScope where

open import Scope
open import Utils.Tactics using (auto)
open import Haskell.Prelude hiding (All; s; t)

open import Agda.Core.Name

record Globals : Set where
  no-eta-equality
  field
    defScope     : Scope Name
    dataScope    : Scope Name
    dataParScope : NameIn dataScope → RScope Name
    dataIxScope  : NameIn dataScope → RScope Name
    conScope     : Scope Name
    fieldScope   : NameIn conScope → RScope Name
open Globals public
{-# COMPILE AGDA2HS Globals #-}

