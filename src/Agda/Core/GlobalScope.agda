module Agda.Core.GlobalScope where

open import Agda.Core.Prelude
open import Agda.Core.Name

record Globals : Set where
  no-eta-equality
  field
    defScope          : Scope Name
    dataScope         : Scope Name
    dataParScope      : NameIn dataScope → RScope Name
    dataIxScope       : NameIn dataScope → RScope Name
    dataConstructors  : NameIn dataScope → RScope Name                                          -- TODO: change RScope for an erased list
    fieldScope        : {d : NameIn dataScope } → NameInR (dataConstructors d) → RScope Name
    recScope          : Scope Name
    recParScope       : NameIn recScope → RScope Name
  NameData : Set
  NameData = NameIn dataScope
  NameCon : NameData → Set
  NameCon d = NameInR (dataConstructors d)
  NameRec : Set
  NameRec = NameIn recScope
  opaque
    unfolding RScope
    AllNameCon : (d : NameData) → RScope (NameCon d)
    AllNameCon d = rScopeToRScopeNameInR (dataConstructors d)
open Globals public

{-# COMPILE AGDA2HS NameData inline #-}
{-# COMPILE AGDA2HS NameCon inline #-}
{-# COMPILE AGDA2HS Globals #-}
