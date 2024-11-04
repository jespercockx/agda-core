open import Scope

open import Haskell.Prelude hiding (All; s; t)
open import Haskell.Extra.Erase
open import Haskell.Law.Equality renaming (subst to transport)

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

private variable
  @0 x : Name
  @0 α0 α α' β γ : Scope Name


{- A module where :
    - auxiliary datatypes are defined for the two telescopic equality
    - equivalence between the auxiliary datatypes for telescopic equality is proved
   Read it if you want to understand the structure behind telescopic equality.
-}
module TelescopeEq where

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
      TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ (ExtendTel x A Δ)

    expandedToCompact : Expanded α0 α β → Compact α0 α β
    expandedToCompact (TelEq ⌈⌉ ⌈⌉ EmptyTel) = EmptyEq
    expandedToCompact (TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ (ExtendTel x A Δ)) = do
      let ΔEq = expandedToCompact (TelEq δ₁ δ₂ Δ)
      ExtendEq x u v A ΔEq

    {- The functions above form an equivalence -}
    equivLeft : (ΔEq : Compact α0 α β)
      → expandedToCompact (compactToExpanded ΔEq) ≡ ΔEq
    equivLeft EmptyEq = refl
    equivLeft (ExtendEq x u v A ΔEq) = do
      let eH = equivLeft ΔEq
      cong (λ ΔEq → ExtendEq x u v A ΔEq) eH

    equivRight : (ΔEq' : Expanded α0 α β)
      → compactToExpanded (expandedToCompact ΔEq') ≡ ΔEq'
    equivRight (TelEq ⌈⌉ ⌈⌉ EmptyTel) = refl
    equivRight (TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ (ExtendTel x A Δ)) = do
      let eH = equivRight (TelEq δ₁ δ₂ Δ)
      cong (λ (TelEq δ₁ δ₂ Δ) → TelEq (SCons u δ₁) (SCons v δ₂) (ExtendTel x A Δ)) eH

{- End of module TelescopeEq -}


telescopicEq : (@0 α β : Scope Name) → Set
telescopicEq α β = TelescopeEq.Compact α mempty β

telescopicEq' : (@0 α β : Scope Name) → Set
telescopicEq' α β = TelescopeEq.Expanded α mempty β

telEqCompactToExpanded : telescopicEq α β → telescopicEq' α β
telEqCompactToExpanded ΔEqAux = TelescopeEq.compactToExpanded ΔEqAux

telEqExpandedToCompact : telescopicEq' α β → telescopicEq α β
telEqExpandedToCompact ΔEqAux' = TelescopeEq.expandedToCompact ΔEqAux'

equivTelEqLeft : (ΔEq : telescopicEq α β)
  → telEqExpandedToCompact (telEqCompactToExpanded ΔEq) ≡ ΔEq
equivTelEqLeft ΔEq = TelescopeEq.equivLeft ΔEq

equivTelEqRight : (ΔEq' : telescopicEq' α β)
  → telEqCompactToExpanded (telEqExpandedToCompact ΔEq') ≡ ΔEq'
equivTelEqRight ΔEq' = TelescopeEq.equivRight ΔEq'
