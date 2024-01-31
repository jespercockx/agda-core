open import Scope

open import Haskell.Prelude hiding (All; s; t)
open import Haskell.Extra.Dec using (ifDec)

open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Utils renaming (_,_ to _Σ,_)

module Agda.Core.Signature {@0 name  : Set} (@0 globals : Globals name) where

open import Agda.Core.Syntax globals
private open module @0 G = Globals globals

private variable
  @0 α β : Scope name

data Telescope (@0 α : Scope name) : @0 Scope name → Set where
  EmptyTel  : Telescope α mempty
  ExtendTel : (@0 x : name) → Type α → Telescope (x ◃ α) β  → Telescope α (x ◃ β)

{-# COMPILE AGDA2HS Telescope #-}

opaque
  unfolding Scope
  caseTelBind : {@0 x : name}
                (P : @0 Telescope α (x ◃ β) → Set)
                (tel : Telescope α (x ◃ β))
              → ((a : Type α) (tel : Telescope (x ◃ α) β) → P (ExtendTel x a tel))
              → P tel
  caseTelBind P (ExtendTel _ a tel) f = f a tel

record Constructor (@0 pars : Scope name) (@0 ixs : Scope name) (@0 c : name) (@0 cp  : c ∈ conScope) : Set where
  field
    conTelescope : Telescope pars (lookupAll fieldScope cp)
    conIndices   : ixs ⇒ (lookupAll fieldScope cp <> pars)
open Constructor public

{-# COMPILE AGDA2HS Constructor #-}

record Datatype : Set where
  field
    @0 dataParameterScope   : Scope name
    @0 dataIndexScope       : Scope name
    @0 dataConstructorScope : Scope name
    dataSort                : Sort dataParameterScope
    dataParameterTel        : Telescope mempty dataParameterScope
    dataIndexTel            : Telescope dataParameterScope dataIndexScope
    dataConstructors        : All (λ c → Σ (c ∈ conScope) (Constructor dataParameterScope dataIndexScope c)) dataConstructorScope
open Datatype public

{-# COMPILE AGDA2HS Datatype #-}

data Definition : Set where
  FunctionDef : (funBody : Term mempty) → Definition
  DatatypeDef : (datatypeDef : Datatype) → Definition
  RecordDef   : {- TODO → -} Definition

{-# COMPILE AGDA2HS Definition #-}

Signature : Set
Signature = All (λ _ → Type (mempty {{iMonoidScope}}) × Definition) defScope

{-# COMPILE AGDA2HS Signature #-}

getType : Signature → (@0 x : name) → x ∈ defScope → Type mempty
getType sig x p = fst (lookupAll sig p)

{-# COMPILE AGDA2HS getType #-}

getDefinition : Signature → (@0 x : name) → x ∈ defScope → Definition
getDefinition sig x p = snd (lookupAll sig p)

{-# COMPILE AGDA2HS getDefinition #-}

getBody : Signature → (@0 x : name) → x ∈ defScope → Maybe (Term mempty)
getBody sig x p = case getDefinition sig x p of λ where
  (FunctionDef body) → Just body
  (DatatypeDef _)    → Nothing
  RecordDef          → Nothing

{-# COMPILE AGDA2HS getBody #-}

getConstructor : (@0 c : name) (cp : c ∈ conScope) (d : Datatype) → Maybe (Constructor (dataParameterScope d) (dataIndexScope d) c cp)
getConstructor c cp d =
  findAll (allIn $ dataConstructors d) λ where
    (cpn Σ, con , _) ret → ifDec (decIn cp cpn) (λ where {{refl}} → Just con) Nothing

{-# COMPILE AGDA2HS getConstructor #-}
