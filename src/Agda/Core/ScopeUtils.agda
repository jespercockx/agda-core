open import Haskell.Prelude
open import Haskell.Extra.Erase
open import Haskell.Law.Equality

open import Scope


open import Agda.Core.Name

module Agda.Core.ScopeUtils where

private variable
  @0 α : Scope Name

opaque
  unfolding Sub Split
  @0 cut : {α : Scope Name} → NameIn α → Scope Name × Scope Name
  cut (⟨ _ ⟩ ⟨ _ ⟩ EmptyR) = mempty , mempty
  cut {α = _ ∷ α'} (⟨ x ⟩ ⟨ _ ⟩ ConsL .x _) = α' , mempty
  cut {α = Erased y ∷ _} (⟨ x ⟩ ⟨ _ ⟩ ConsR .y p) = do
    let α₀ , α₁ = cut (⟨ x ⟩ ⟨ _ ⟩ p)
    α₀ , Erased y ∷ α₁

@0 cutDrop : NameIn α → Scope Name
cutDrop x = fst (cut x)

@0 cutTake : NameIn α → Scope Name
cutTake x = snd (cut x)

opaque
  unfolding cut
  @0 cutEq : (x : NameIn α) → cutTake x <> (proj₁ x ◃ cutDrop x) ≡ α
  cutEq (⟨ _ ⟩ ⟨ _ ⟩ EmptyR) = refl
  cutEq (⟨ x ⟩ ⟨ _ ⟩ ConsL .x _) = refl
  cutEq {α = Erased y ∷ α'} (⟨ x ⟩ ⟨ _ ⟩ ConsR .y p) = cong (λ α → Erased y ∷ α ) (cutEq (⟨ x ⟩ ⟨ _ ⟩ p))

  cutSplit : (x : NameIn α) → cutTake x ⋈ (proj₁ x ◃ cutDrop x) ≡ α
  cutSplit (⟨ _ ⟩ ⟨ _ ⟩ EmptyR) = EmptyL
  cutSplit (⟨ x ⟩ ⟨ _ ⟩ ConsL .x p) = EmptyL
  cutSplit {α = Erased y ∷ α'} (⟨ x ⟩ ⟨ _ ⟩ ConsR .y p) = ConsL y (cutSplit (⟨ x ⟩ ⟨ _ ⟩ p))

rezzCutDrop : {x : NameIn α} → Rezz α → Rezz (cutDrop x)
rezzCutDrop αRun = rezzUnbind (rezzSplitRight (cutSplit _) αRun)

rezzCutTake : {x : NameIn α} → Rezz α → Rezz (cutTake x)
rezzCutTake αRun =  rezzSplitLeft (cutSplit _) αRun


subCut :  {x : NameIn α} → Rezz α → (cutTake x <> cutDrop x) ⊆ α
subCut {x = x} αRun =
    subst0 (λ α' → (cutTake x <> cutDrop x) ⊆ α')
        (cutEq x) (subJoin (rezzCutTake αRun) subRefl (subBindDrop subRefl))

subCutDrop :  {x : NameIn α} →  cutDrop x ⊆ α
subCutDrop = subTrans (subBindDrop subRefl) (subRight (cutSplit _))

subCutTake :  {x : NameIn α} →  cutTake x ⊆ α
subCutTake = subLeft (cutSplit _)