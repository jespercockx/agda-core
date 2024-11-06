open import Scope

open import Haskell.Prelude hiding (All; s; t)
open import Haskell.Extra.Erase
open import Haskell.Law.Equality renaming (subst to transport)
open import Haskell.Law.Semigroup.Def

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Utils
open import Agda.Core.Syntax
open import Agda.Core.Signature
open import Agda.Core.Substitute
open import Agda.Core.Context
open import Agda.Core.Typing


module Agda.Core.Unification
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

---------------------------------------------------------------------------------------------------
                        {- PART ONE : Definition of telescopic equality -}
---------------------------------------------------------------------------------------------------


module TelescopeEq where
  {- A module where :
    - auxiliary datatypes are defined for the two telescopic equality
    - equivalence between the auxiliary datatypes for telescopic equality is proved
   Read it if you want to understand the structure behind telescopic equality.
  -}

  private variable
    @0 x : Name
    @0 α0 α β : Scope Name

  {- Compact version of telescopic equality, where both parts of the equality are constructed step by step -}
  data Compact (@0 α0 : Scope Name) : (@0 α β : Scope Name) → Set where
    EmptyEq : Compact α0 α mempty
    ExtendEq : {@0 β : Scope Name} (@0 x : Name)
      (u v : Term α0) (A : Type (α <> α0))
      → Compact α0 (x ◃ α) β
      → Compact α0 α (x ◃ β)

  {- Expanded version of telescopic equality, where both parts of the equality are already constructed -}
  record Expanded (@0 α0 α β : Scope Name) : Set where
    constructor TelEq
    field
      left : β ⇒ α0
      right : β ⇒ α0
      telescope : Telescope (α <> α0) β

  {- Functions to go from one version to the other -}
  opaque
    unfolding Scope
    compactToExpanded : Compact α0 α β → Expanded α0 α β
    compactToExpanded EmptyEq = TelEq ⌈⌉ ⌈⌉ EmptyTel
    compactToExpanded (ExtendEq x u v A ΔEq) = do
      let TelEq δ₁ δ₂ Δ = compactToExpanded ΔEq
      TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ A ◃ Δ ⌉

    expandedToCompact : Expanded α0 α β → Compact α0 α β
    expandedToCompact (TelEq ⌈⌉ ⌈⌉ EmptyTel) = EmptyEq
    expandedToCompact (TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ A ◃ Δ ⌉) = do
      let ΔEq = expandedToCompact (TelEq δ₁ δ₂ Δ)
      ExtendEq x u v A ΔEq

  {-
  {- it doesn't work : another version but without unfolding scope -}
  compactToExpanded : Compact α0 α β → Expanded α0 α β
  compactToExpanded EmptyEq = TelEq ⌈⌉ ⌈⌉ EmptyTel
  compactToExpanded {α0} {α} (ExtendEq x u v A ΔEq) = do
    let TelEq δ₁ δ₂ Δ = compactToExpanded ΔEq
        Δ' = subst0 (λ γ → Telescope γ _)
          (sym (IsLawfulSemigroup.associativity iLawfulSemigroupScope [ x ] α α0)) Δ
    TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ (ExtendTel x A Δ')
  opaque
    unfolding Scope
    caseConsBind : (σ : (x ◃ α) ⇒ β)
               → ((a : Term β) (rest : α ⇒ β) → @0 {{σ ≡ ⌈ x ↦ a ◃ rest ⌉}} → d)
                → d
    caseConsBind ⌈ x ↦ u ◃ σ ⌉ f = f u σ

  expandedToCompact : Expanded α0 α β → Compact α0 α β
  expandedToCompact (TelEq ⌈⌉ _ _) = EmptyEq
  expandedToCompact {α0} {α} (TelEq ⌈ x ↦ u ◃ δ₁ ⌉ δ₂ Δ) = do
    let telSubst = subst0 (λ γ → Telescope γ _)
          (IsLawfulSemigroup.associativity iLawfulSemigroupScope [ x ] α α0)
        res = λ δ₂' v A Δ₀ → ExtendEq x u v A (expandedToCompact (TelEq δ₁ δ₂' (telSubst Δ₀)))
    caseConsBind δ₂
      λ where v δ₂ ⦃ refl ⦄ →
                caseTelBind Δ λ where A Δ₀ ⦃ refl ⦄ → res δ₂ v A Δ₀
  -}
    {- The functions above form an equivalence -}
    equivLeft : (ΔEq : Compact α0 α β)
      → expandedToCompact (compactToExpanded ΔEq) ≡ ΔEq
    equivLeft EmptyEq = refl
    equivLeft (ExtendEq x u v A ΔEq) = do
      let eH = equivLeft ΔEq
      cong (λ ΔEq → ExtendEq x u v A ΔEq) eH

    equivRight : (ΔEq' : Expanded α0 α β)
      → compactToExpanded (expandedToCompact ΔEq') ≡ ΔEq'
    equivRight (TelEq ⌈⌉ ⌈⌉ ⌈⌉) = refl
    equivRight (TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ A ◃ Δ ⌉) = do
      let eH = equivRight (TelEq δ₁ δ₂ Δ)
      cong (λ (TelEq δ₁ δ₂ Δ) → TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ A ◃ Δ ⌉) eH

    equivalence : Equivalence (Compact α0 α β) (Expanded α0 α β)
    equivalence = Equiv compactToExpanded expandedToCompact equivLeft equivRight

{- End of module TelescopeEq -}

telescopicEq : (@0 α β : Scope Name) → Set
telescopicEq α β = TelescopeEq.Compact α mempty β

pattern ⌈⌉ = TelescopeEq.EmptyEq
infix 6 ⌈_≟_∶_◃_⌉
pattern ⌈_≟_∶_◃_⌉ = TelescopeEq.ExtendEq


telescopicEq' : (@0 α β : Scope Name) → Set
telescopicEq' α β = TelescopeEq.Expanded α mempty β

equivalenceTelEq : {@0 α β : Scope Name} → Equivalence (telescopicEq α β) (telescopicEq' α β)
equivalenceTelEq = TelescopeEq.equivalence

---------------------------------------------------------------------------------------------------
                            {- PART TWO : Unification Step By Step -}
---------------------------------------------------------------------------------------------------
