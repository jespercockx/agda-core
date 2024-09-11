
open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Scope

module Agda.Core.Name where

Name = String
{-# COMPILE AGDA2HS Name inline #-}

NameIn : (@0 α : Scope Name) → Set
NameIn α = Σ0 Name λ x → x ∈ α
{-# COMPILE AGDA2HS NameIn inline #-}

decNamesIn : ∀ {@0 α} (x y : NameIn α) → Dec (x ≡ y)
decNamesIn x y = decIn _ _
{-# COMPILE AGDA2HS decNamesIn inline #-}

ifEqualNamesIn : ∀ {@0 α} (x y : NameIn α)
               → (@0 {{x ≡ y}} → b) → (@0 {{x ≡ y → ⊥}} → b) → b
ifEqualNamesIn x y = ifDec (decNamesIn x y)
{-# COMPILE AGDA2HS ifEqualNamesIn inline #-}

nameInEmptyCase : NameIn mempty → a
nameInEmptyCase x = inEmptyCase (proj₂ x)
{-# COMPILE AGDA2HS nameInEmptyCase inline #-}

nameInBindCase : ∀ {@0 y α} (x : NameIn (y ◃ α)) → (@0 proj₁ x ≡ y → a) → (proj₁ x ∈ α → a) → a
nameInBindCase x = inBindCase (proj₂ x)
{-# COMPILE AGDA2HS nameInBindCase inline #-}
