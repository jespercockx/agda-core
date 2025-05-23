open import Haskell.Prelude hiding (All; c; d; s; t)
open import Haskell.Extra.Erase
open import Haskell.Law.Equality      using (subst0; sym)
open import Haskell.Law.Semigroup.Def using (associativity)
open import Haskell.Law.Monoid.Def

open import Agda.Core.Name
open import Agda.Core.Utils

open import Agda.Core.Syntax.Term
open import Agda.Core.Syntax.Context
open import Agda.Core.Syntax.Weakening
open import Agda.Core.Syntax.Substitute


module Agda.Core.Syntax.Signature {{@0 globals : Globals}} where

private open module @0 G = Globals globals

private variable
  @0 α  : Scope Name
  @0 d  : NameData
---------------------------------------------------------------------------------------------------
                                        {- Constructor -}
---------------------------------------------------------------------------------------------------
record Constructor {@0 d : NameData} (@0 c : NameCon d) : Set where
  private
    @0 pars : RScope Name
    pars = dataParScope d
    @0 ixs : RScope Name
    ixs  = dataIxScope d
  field
    conIndTel : Telescope (extScope mempty pars) (fieldScope c)
    -- the TypeS of the indexes of c
    conIx     :  TermS (extScope (extScope mempty pars) (fieldScope c)) ixs
    -- how the indexes are constructred given parameters and c indices

  instConIndTel : TermS α (dataParScope d) → Telescope α (fieldScope c)
  instConIndTel tPars = subst (extSubst ⌈⌉ tPars) conIndTel
  {-# COMPILE AGDA2HS instConIndTel inline #-}

open Constructor public
{-# COMPILE AGDA2HS Constructor #-}

instConIx : {@0 c : NameCon d} (con : Constructor c)
  → TermS α (dataParScope d) → TermS α (fieldScope c) → TermS α (dataIxScope d)
instConIx con tPars tInd = subst (extSubst (extSubst ⌈⌉ tPars) tInd) (conIx con)
{-# COMPILE AGDA2HS instConIx #-}

---------------------------------------------------------------------------------------------------
                                          {- Datatype -}
---------------------------------------------------------------------------------------------------
record Datatype (@0 d : NameData) : Set where
  private
    @0 pars : RScope Name
    pars = dataParScope d
    @0 ixs : RScope Name
    ixs  = dataIxScope d
  field
    dataSort             : Sort (extScope mempty pars)
    dataParTel           : Telescope mempty pars
    dataIxTel            : Telescope (extScope mempty pars) ixs
    dataConstructors     : List (NameCon d) -- for Haskell side

  instDataSort : TermS α (dataParScope d) → Sort α
  instDataSort tPars = subst (extSubst ⌈⌉ tPars) dataSort
  {-# COMPILE AGDA2HS instDataSort inline #-}

  instDataParTel : Telescope α (dataParScope d)
  instDataParTel = subst ⌈⌉ dataParTel
  {-# COMPILE AGDA2HS instDataParTel inline #-}

  instDataIxTel : TermS α (dataParScope d) → Telescope α (dataIxScope d)
  instDataIxTel tPars = subst (extSubst ⌈⌉ tPars) dataIxTel
  {-# COMPILE AGDA2HS instDataIxTel inline #-}

open Datatype public
{-# COMPILE AGDA2HS Datatype #-}

---------------------------------------------------------------------------------------------------
                                          {- Signature -}
---------------------------------------------------------------------------------------------------
data SigDefinition : Set where
  FunctionDef : (funBody : Term mempty) → SigDefinition
{-# COMPILE AGDA2HS SigDefinition #-}

record Signature : Set where
  field
    sigData : (d : NameData) → Datatype d
    sigDefs : (f : NameIn defScope)  → Type mempty × SigDefinition
    sigCons : (d : NameData) (c : NameCon d) → Constructor c
    -- Do not erase d, (d,c) is needed to find the constructor

open Signature public
{-# COMPILE AGDA2HS Signature #-}

getType : Signature → (x : NameIn defScope) → Type α
getType sig x = subst ⌈⌉ (fst defs)
  where
    -- inlining this seems to trigger a bug in agda2hs
    -- TODO: investigate further
    defs = sigDefs sig x
{-# COMPILE AGDA2HS getType #-}

getDefinition : Signature → (x : NameIn defScope) → SigDefinition
getDefinition sig x = snd defs
  where
    -- see above
    defs = sigDefs sig x
{-# COMPILE AGDA2HS getDefinition #-}

getBody : Signature → (x : NameIn defScope) → Term mempty
getBody sig x = case getDefinition sig x of λ where
  (FunctionDef body) → body
{-# COMPILE AGDA2HS getBody #-}

---------------------------------------------------------------------------------------------------
                                          {- Haskell -}
---------------------------------------------------------------------------------------------------
{- Definitions for haskell part -}
data Defn : Set where
  FunctionDefn : (funBody : Term mempty) → Defn
  DatatypeDefn :  (@0 d : NameData) → Datatype d → Defn
  ConstructorDefn : (@0 d : NameData) (@0 c : NameCon d) → Constructor c → Defn
{-# COMPILE AGDA2HS Defn #-}


record Definition : Set where
  field
    defName : String
    defType : Type mempty
    theDef : Defn
open Definition public
{-# COMPILE AGDA2HS Definition #-}
