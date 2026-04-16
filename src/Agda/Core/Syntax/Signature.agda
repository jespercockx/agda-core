
open import Agda.Core.Prelude
open import Agda.Core.Name

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
                                        {- DataConstructor -}
---------------------------------------------------------------------------------------------------

record DataConstructor {@0 d : NameData} (@0 c : NameCon d) : Set where
  no-eta-equality
  private
    @0 pars : RScope Name
    pars = dataParScope d
    @0 ixs : RScope Name
    ixs  = dataIxScope d
  field
    conIndTel : Telescope (mempty ◂▸ pars) (dataFieldScope c)
    -- the TypeS of the indices of c
    conIx     :  TermS (mempty ◂▸ pars ◂▸ dataFieldScope c) ixs
    -- how the indices are constructed given parameters and c indices

  instConIndTel : TermS α (dataParScope d) → Telescope α (dataFieldScope c)
  instConIndTel tPars = subst (extSubst ⌈⌉ tPars) conIndTel
  {-# COMPILE AGDA2HS instConIndTel inline #-}

open DataConstructor public
{-# COMPILE AGDA2HS DataConstructor #-}

instConIx : {@0 c : NameCon d} (con : DataConstructor c)
  → TermS α (dataParScope d) → TermS α (dataFieldScope c) → TermS α (dataIxScope d)
instConIx con tPars tInd = subst (extSubst (extSubst ⌈⌉ tPars) tInd) (conIx con)
{-# COMPILE AGDA2HS instConIx #-}

---------------------------------------------------------------------------------------------------
                                          {- Datatype -}
---------------------------------------------------------------------------------------------------
record Datatype (@0 d : NameData) : Set where
  no-eta-equality
  private
    @0 pars : RScope Name
    pars = dataParScope d
    @0 ixs : RScope Name
    ixs  = dataIxScope d
  field
    dataSort             : Sort (mempty ◂▸ pars)
    dataParTel           : Telescope mempty pars
    dataIxTel            : Telescope (mempty ◂▸ pars) ixs
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
                                          {- Record -}
---------------------------------------------------------------------------------------------------
record Record (@0 rn : NameRec) : Set where
  no-eta-equality
  private
    @0 pars : RScope Name
    pars = recParScope rn
  field
    recSort         : Sort (mempty ◂▸ pars)
    -- The telescope of all the parameters of the record type
    recParTel       : Telescope mempty pars
    -- The telescope of all the arguments of the record constructor
    recConArgTel    : Telescope (mempty ◂▸ pars) (recFieldScope rn)

  -- instantiated telescope of the record constructor, given some parameters
  instRecConArgTel : TermS α (recParScope rn) → Telescope α (recFieldScope rn)
  instRecConArgTel tPars = subst (extSubst ⌈⌉ tPars) recConArgTel
  {-# COMPILE AGDA2HS instRecConArgTel inline #-}
                                            
  instRecSort : TermS α (recParScope rn) → Sort α
  instRecSort tPars = subst (extSubst ⌈⌉ tPars) recSort
  {-# COMPILE AGDA2HS instRecSort inline #-}

  instRecParTel : Telescope α (recParScope rn)
  instRecParTel = subst ⌈⌉ recParTel
  {-# COMPILE AGDA2HS instRecParTel inline #-}


open Record public
{-# COMPILE AGDA2HS Record #-}

-- ---------------------------------------------------------------------------------------------------
--                                           {- Projection function -}
-- ---------------------------------------------------------------------------------------------------
-- record ProjectionFunction {@0 rn : NameRec} (@0 proj : NameProj rn) : Set where
--   no-eta-equality
--   private
--     @0 pars : RScope Name
--     pars = recParScope rn
--   field
--     recSort         : Sort (mempty ◂▸ pars)
-- open ProjectionFunction public
-- {-# COMPILE AGDA2HS ProjectionFunction #-}

-- ---------------------------------------------------------------------------------------------------
--                                           {- Record constructor -}
-- ---------------------------------------------------------------------------------------------------
-- record RecConstructor {@0 rn : NameRec} (@0 c : NameRecCon rn) : Set where
--   no-eta-equality
--   private
--     @0 pars : RScope Name
--     pars = recParScope rn
--   field
--     recSort         : Sort (mempty ◂▸ pars)
-- open RecConstructor public
-- {-# COMPILE AGDA2HS RecConstructor #-}

---------------------------------------------------------------------------------------------------
                                          {- Signature -}
---------------------------------------------------------------------------------------------------
data SigDefinition : Set where
  FunctionDef : (funBody : Term mempty) → SigDefinition
  ProjectionDef : SigDefinition
{-# COMPILE AGDA2HS SigDefinition #-}

record Signature : Set where
  no-eta-equality
  field
    sigData : (d : NameData) → Datatype d
    sigDefs : (f : NameIn defScope)  → Type mempty × SigDefinition
    -- Do not erase d, (d,c) is needed to find the constructor
    sigCons : (d : NameData) (c : NameCon d) → DataConstructor c
    sigRecs : (recordName : NameRec) → Record recordName
    -- sigRecCons : (rn : NameRec) (c : NameRecCon rn) → RecConstructor c
    -- sigProjFuncs : (rn : NameRec) (proj : NameProj rn) → ProjectionFunction proj

open Signature public
{-# COMPILE AGDA2HS Signature #-}

getType : Signature → (x : NameIn defScope) → Type α
getType sig x = subst ⌈⌉ (fst typeAndSigDef)
  where
    -- inlining this seems to trigger a bug in agda2hs
    -- TODO: investigate further
    typeAndSigDef = sigDefs sig x
{-# COMPILE AGDA2HS getType #-}

getDefinition : Signature → (x : NameIn defScope) → SigDefinition
getDefinition sig x = snd typeAndSigDef
  where
    -- see above
    typeAndSigDef = sigDefs sig x
{-# COMPILE AGDA2HS getDefinition #-}

getBody : Signature → (x : NameIn defScope) → Maybe (Term mempty)
getBody sig x = case getDefinition sig x of λ where
  (FunctionDef body) → Just body
  ProjectionDef → Nothing
{-# COMPILE AGDA2HS getBody #-}

---------------------------------------------------------------------------------------------------
                                          {- Haskell -}
---------------------------------------------------------------------------------------------------
{- Definitions for haskell part -}
data Defn : Set where
  FunctionDefn : (funBody : Term mempty) → Defn
  DatatypeDefn :  (@0 d : NameData) → Datatype d → Defn
  DataConstructorDefn : (@0 d : NameData) (@0 c : NameCon d) → DataConstructor c → Defn
  RecordDefn : (@0 r : NameRec) → Record r → Defn
  RecordConstructorDefn : Defn
  ProjDefn : Defn
{-# COMPILE AGDA2HS Defn #-}


record Definition : Set where
  no-eta-equality
  field
    defName : String
    defType : Type mempty
    theDef : Defn
open Definition public
{-# COMPILE AGDA2HS Definition #-}
