module Agda.Core.GlobalScope where

open import Scope
open import Haskell.Prelude hiding (All; s; t)

Name = String

record Globals : Set where
  field
    defScope   : Scope Name
    conScope   : Scope Name
    fieldScope : All (λ _ → Scope Name) conScope
open Globals public
{-# COMPILE AGDA2HS Globals #-}

