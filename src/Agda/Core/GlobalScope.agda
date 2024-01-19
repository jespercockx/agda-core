module Agda.Core.GlobalScope (@0 name  : Set) where

open import Scope
open import Haskell.Prelude hiding (All; s; t)

record Globals : Set where
  field
    defScope   : Scope name
    conScope   : Scope name
    fieldScope : All (λ _ → Scope name) conScope
open Globals public
{-# COMPILE AGDA2HS Globals #-}
