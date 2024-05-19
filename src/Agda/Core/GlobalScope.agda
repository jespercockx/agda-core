module Agda.Core.GlobalScope (@0 name  : Set) where

open import Scope
open import Haskell.Prelude hiding (All; s; t)

record Globals : Set where
  field
    defScope   : Scope name
    datScope   : Scope name
    conScope   : Scope name
    --TODO rename to cargScope?
    fieldScope : All (λ _ → Scope name) conScope
    paramScope : All (λ _ → Scope name) datScope
    indexScope : All (λ _ → Scope name) datScope
open Globals public
{-# COMPILE AGDA2HS Globals #-}
