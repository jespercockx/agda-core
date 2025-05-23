open import Haskell.Prelude
open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement

module Agda.Core.Name where

open import Scope public

Name = String
{-# COMPILE AGDA2HS Name inline #-}

NameIn : (@0 α : Scope Name) → Set
NameIn α = Σ0 Name λ x → x ∈ α
{-# COMPILE AGDA2HS NameIn inline #-}

NameInR : (@0 rα : RScope Name) → Set
NameInR rα = Σ0 Name λ x → rα ∋ x
{-# COMPILE AGDA2HS NameInR inline #-}

decNamesIn : ∀ {@0 α} (x y : NameIn α) → Dec (x ≡ y)
decNamesIn x y = decIn _ _
{-# COMPILE AGDA2HS decNamesIn inline #-}

decNamesInR : ∀ {@0 rα} (x y : NameInR rα) → Dec (x ≡ y)
decNamesInR x y = decInR _ _
{-# COMPILE AGDA2HS decNamesInR inline #-}

ifEqualNamesIn : ∀ {@0 α} (x y : NameIn α)
               → (@0 {{x ≡ y}} → b) → (@0 {{x ≡ y → ⊥}} → b) → b
ifEqualNamesIn x y = ifDec (decNamesIn x y)
{-# COMPILE AGDA2HS ifEqualNamesIn inline #-}

nameInEmptyCase : NameIn mempty → a
nameInEmptyCase x = inEmptyCase (proj₂ x)
{-# COMPILE AGDA2HS nameInEmptyCase inline #-}

nameInBindCase : ∀ {@0 y α} (x : NameIn (α ▸ y)) → (proj₁ x ∈ α → a) → (@0 proj₁ x ≡ y → a) → a
nameInBindCase x = inBindCase (proj₂ x)
{-# COMPILE AGDA2HS nameInBindCase inline #-}

private variable
  @0 α : Scope Name

indexToNat : Index → Nat
indexToNat Zero = zero
indexToNat (Suc n) = suc (indexToNat n)

natToIndex : Nat → Index
natToIndex zero = Zero
natToIndex (suc n) = Suc (natToIndex n)

instance
  iEqForIndex : Eq Index
  iEqForIndex ._==_  = λ n m → (indexToNat n) == (indexToNat m)

instance
  iOrdFromLessThanIndex : OrdFromLessThan Index
  iOrdFromLessThanIndex .OrdFromLessThan._<_ = λ n m → (indexToNat n) < (indexToNat m)

  iOrdIndex : Ord Index
  iOrdIndex = record
    { OrdFromLessThan iOrdFromLessThanIndex
    ; max = λ n m → natToIndex (max (indexToNat n) (indexToNat m))
    ; min = λ n m → natToIndex (min (indexToNat n) (indexToNat m))
    }



eqNameIn : NameIn α → NameIn α → Bool
eqNameIn (⟨ _ ⟩ (n ⟨ _ ⟩)) (⟨ _ ⟩ (m ⟨ _ ⟩)) = n == m

ltNameIn : NameIn α → NameIn α → Bool
ltNameIn (⟨ _ ⟩ (n ⟨ _ ⟩)) (⟨ _ ⟩ (m ⟨ _ ⟩)) = n < m

maxNameIn : NameIn α → NameIn α → NameIn α
maxNameIn (⟨ x ⟩ (n ⟨ xp ⟩)) (⟨ y ⟩ (m ⟨ yp ⟩)) with ((max n m) == n)
... | True = ⟨ x ⟩ (n ⟨ xp ⟩)
... | False = ⟨ y ⟩ (m ⟨ yp ⟩)

minNameIn : NameIn α → NameIn α → NameIn α
minNameIn (⟨ x ⟩ (n ⟨ xp ⟩)) (⟨ y ⟩ (m ⟨ yp ⟩)) with ((min n m) == n)
... | True = ⟨ x ⟩ (n ⟨ xp ⟩)
... | False = ⟨ y ⟩ (m ⟨ yp ⟩)

instance
  iEqForNameIn : Eq (NameIn α)
  iEqForNameIn  ._==_  = eqNameIn

instance
  iOrdFromLessThanNameIn : OrdFromLessThan (NameIn α)
  iOrdFromLessThanNameIn .OrdFromLessThan._<_ = ltNameIn

  iOrdNameIn : Ord (NameIn α)
  iOrdNameIn = record
    { OrdFromLessThan iOrdFromLessThanNameIn
    ; max = maxNameIn
    ; min = minNameIn
    }

-------------------------------------------------------------------------------
pattern Vsuc n p = ⟨ _ ⟩ (Suc n ⟨ IsSuc p ⟩)
pattern V2suc n p = ⟨ _ ⟩ (Suc (Suc n) ⟨ IsSuc (IsSuc p) ⟩)
pattern Vzero = ⟨ _ ⟩ Zero ⟨ IsZero refl ⟩
pattern Vone = ⟨ _ ⟩ (Suc Zero) ⟨ IsSuc (IsZero refl) ⟩
-------------------------------------------------------------------------------
