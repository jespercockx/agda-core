open import Scope

open import Haskell.Prelude hiding (All; s; t)

open import Agda.Core.GlobalScope using (Globals)

module Agda.Core.Signature {@0 name  : Set} (@0 globals : Globals name) where

open import Agda.Core.Syntax globals
private open module @0 G = Globals globals

private variable
  @0 α β : Scope name

{-
data Telescope (α : Scope name) : Scope name → Set where
  EmptyTel  : Telescope α mempty
  ExtendTel : (@0 x : name) → Type α → Telescope (x ◃ α) β → Telescope α (x ◃ β)

record Constructor (pars : Scope name) (ixs : Scope name) : Set where
  field
    @0 conName : name
    conPosition : conName ∈ conScope
    conTelescope : Telescope pars (lookupAll fieldScope conPosition)
    conIndices : Environment ? ?
-}

data Definition : Set where
  Function : (funBody : Term mempty) → Definition
  Datatype : {- TODO → -} Definition
  Record   : {- TODO → -} Definition

{-# COMPILE AGDA2HS Definition #-}

Signature : Set
Signature = All (λ _ → Type (mempty {{iMonoidScope}}) × Definition) defScope

{-# COMPILE AGDA2HS Signature #-}

getType : Signature → (@0 x : name) → x ∈ defScope → Type mempty
getType sig x p = fst (lookupAll sig p)

{-# COMPILE AGDA2HS getType #-}

getBody : Signature → (@0 x : name) → x ∈ defScope → Maybe (Term mempty)
getBody sig x p = case snd (lookupAll sig p) of λ where
  (Function body) → Just body
  Datatype        → Nothing
  Record          → Nothing

{-# COMPILE AGDA2HS getBody #-}
