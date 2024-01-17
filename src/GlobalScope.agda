
open import Scope

open import Haskell.Prelude hiding (All; s; t)

module GlobalScope {@0 name  : Set} where

record Globals : Set where
  field
    defScope   : Scope name
    conScope   : Scope name
    fieldScope : All (λ _ → Scope name) conScope
