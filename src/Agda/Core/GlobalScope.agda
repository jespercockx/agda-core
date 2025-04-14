module Agda.Core.GlobalScope where

open import Scope
open import Utils.Tactics using (auto)
open import Haskell.Prelude hiding (All; s; t)
open import Haskell.Extra.Erase

open import Agda.Core.Name

record Globals : Set where
  no-eta-equality
  field
    defScope          : Scope Name
    dataScope         : Scope Name                                                              -- why a Scope and not a list ?
    dataParScope      : NameIn dataScope → RScope Name
    dataIxScope       : NameIn dataScope → RScope Name
    dataConstructors  : NameIn dataScope → RScope Name                                          -- why a RScope and not a list ?
    fieldScope        : {d : NameIn dataScope } → NameInR (dataConstructors d) → RScope Name
  NameData : Set
  NameData = NameIn dataScope
  {-# COMPILE AGDA2HS NameData inline #-}
  NameCon : NameData → Set
  NameCon d = NameInR (dataConstructors d)
  {-# COMPILE AGDA2HS NameCon inline #-}
  opaque
    unfolding RScope
    AllNameCon : (d : NameData) → RScope (NameCon d)
    AllNameCon d = levelup (dataConstructors d)
      where levelup : (rα : RScope Name) → RScope (NameInR rα)
            levelup [] = []
            levelup (Erased x ∷ s)  = Erased (⟨ x ⟩ inRHere) ∷ map (λ where (Erased (⟨ _ ⟩ t)) → Erased (⟨ _ ⟩ (inRThere t))) (levelup s)
open Globals public
{-# COMPILE AGDA2HS Globals #-}
