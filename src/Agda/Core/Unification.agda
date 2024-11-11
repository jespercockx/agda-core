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


module Agda.Core.Unification
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x : Name
  @0 α α' β β' : Scope Name

---------------------------------------------------------------------------------------------------
                        {- PART ONE : Context manipulation -}
---------------------------------------------------------------------------------------------------

data ShrinkSubst : (@0 α β : Scope Name) → Set where
  RNil  : ShrinkSubst mempty mempty
  RKeep : ShrinkSubst α β → ShrinkSubst (x ◃ α) (x ◃ β)
  RCons : Term β → ShrinkSubst α β → ShrinkSubst (x ◃ α) β
{-# COMPILE AGDA2HS ShrinkSubst deriving Show #-}


idShrinkSubst : ShrinkSubst α α
idShrinkSubst = {!   !}


ShrinkSubstToSubst : ShrinkSubst α β → α ⇒ β
ShrinkSubstToSubst RNil = ⌈⌉
ShrinkSubstToSubst (RKeep {x = x} σ) =
  ⌈ x ↦ TVar (⟨ x ⟩ inHere) ◃ weaken (subBindDrop subRefl) (ShrinkSubstToSubst σ) ⌉
ShrinkSubstToSubst (RCons {x = x} u σ) = ⌈ x ↦ u ◃ ShrinkSubstToSubst σ ⌉

opaque
  unfolding Scope
  shrinkContext : Context α → ShrinkSubst α α' → Context α'
  shrinkContext CtxEmpty RNil = CtxEmpty
  shrinkContext (CtxExtend Γ x a) (RKeep σ) =
    CtxExtend (shrinkContext Γ σ) x (subst (ShrinkSubstToSubst σ) a)
  shrinkContext (CtxExtend Γ x a) (RCons u σ) = shrinkContext Γ σ

---------------------------------------------------------------------------------------------------
                        {- PART TWO : Definition of telescopic equality -}
---------------------------------------------------------------------------------------------------


module TelescopeEq where
  {- A module where :
    - auxiliary datatypes are defined for the two telescopic equality
    - equivalence between the auxiliary datatypes for telescopic equality is proved
    - some transport and substitution auxiliary functions for telescopic equality are implemented
   Read it if you want to understand the structure behind telescopic equality.
  -}

  private variable
    @0 α0 : Scope Name

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
    compactToExpanded (ExtendEq x u v a ΔEq) = do
      let TelEq δ₁ δ₂ Δ = compactToExpanded ΔEq
      TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ a ◃ Δ ⌉

    expandedToCompact : Expanded α0 α β → Compact α0 α β
    expandedToCompact (TelEq ⌈⌉ ⌈⌉ EmptyTel) = EmptyEq
    expandedToCompact (TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ a ◃ Δ ⌉) = do
      let ΔEq = expandedToCompact (TelEq δ₁ δ₂ Δ)
      ExtendEq x u v a ΔEq

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
        res = λ δ₂' v a Δ₀ → ExtendEq x u v a (expandedToCompact (TelEq δ₁ δ₂' (telSubst Δ₀)))
    caseConsBind δ₂
      λ where v δ₂ ⦃ refl ⦄ →
                caseTelBind Δ λ where a Δ₀ ⦃ refl ⦄ → res δ₂ v a Δ₀
  -}
    {- The functions above form an equivalence -}
    equivLeft : (ΔEq : Compact α0 α β)
      → expandedToCompact (compactToExpanded ΔEq) ≡ ΔEq
    equivLeft EmptyEq = refl
    equivLeft (ExtendEq x u v a ΔEq) = do
      let eH = equivLeft ΔEq
      cong (λ ΔEq → ExtendEq x u v a ΔEq) eH

    equivRight : (ΔEq' : Expanded α0 α β)
      → compactToExpanded (expandedToCompact ΔEq') ≡ ΔEq'
    equivRight (TelEq ⌈⌉ ⌈⌉ ⌈⌉) = refl
    equivRight (TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ a ◃ Δ ⌉) = do
      let eH = equivRight (TelEq δ₁ δ₂ Δ)
      cong (λ (TelEq δ₁ δ₂ Δ) → TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ a ◃ Δ ⌉) eH

    equivalence : Equivalence (Compact α0 α β) (Expanded α0 α β)
    equivalence = Equiv compactToExpanded expandedToCompact equivLeft equivRight

  ReshapeComp : Rezz α0 → Rezz α' →  Compact α0 α β → α ⇒ α' <> α0 → Compact α0 α' β
  ReshapeComp _ _ EmptyEq _ = EmptyEq
  ReshapeComp α0Run α'Run (ExtendEq x u v A ΔEq) σ = do
    let A' = subst (concatSubst σ (weaken (subJoinDrop α'Run subRefl) (idSubst α0Run))) A
        x◃α'Run = rezzCong (bind x) α'Run
        u' = weaken (subJoinDrop x◃α'Run subRefl) u
        σ' = weaken (subJoin x◃α'Run (subBindDrop subRefl) subRefl) σ
        ΔEq' = ReshapeComp α0Run x◃α'Run ΔEq ⌈ x ↦ u' ◃ σ' ⌉
    ExtendEq x u v A' ΔEq'

  shrinkCompact : Rezz α → Compact α0 α β → ShrinkSubst α0 α' → Compact α' α β
  shrinkCompact _ EmptyEq _ = EmptyEq
  shrinkCompact αRun (ExtendEq x u v A ΔEq) rσ = do
    let σ = ShrinkSubstToSubst rσ
        u' = subst σ u
        v' = subst σ v
        A' = subst (liftSubst αRun σ) A
    ExtendEq x u' v' A' (shrinkCompact (rezzCong (bind x) αRun) ΔEq rσ)

{- End of module TelescopeEq -}

telescopicEq : (@0 α β : Scope Name) → Set
telescopicEq α β = TelescopeEq.Compact α mempty β

pattern ⌈⌉ = TelescopeEq.EmptyEq
infix 6 ⌈_↦_≟_∶_◃_⌉
pattern ⌈_↦_≟_∶_◃_⌉ x u v t ΔEq = TelescopeEq.ExtendEq x u v t ΔEq


telescopicEq' : (@0 α β : Scope Name) → Set
telescopicEq' α β = TelescopeEq.Expanded α mempty β

equivalenceTelEq : {@0 α β : Scope Name} → Equivalence (telescopicEq α β) (telescopicEq' α β)
equivalenceTelEq = TelescopeEq.equivalence

normalizeEq : {@0 α0 α β : Scope Name}
  → Rezz α0 → TelescopeEq.Compact α0 α β → α ⇒ α0 → telescopicEq α0 β
normalizeEq α0Run ΔEq σ =
  TelescopeEq.ReshapeComp α0Run (rezz mempty) ΔEq (weaken (subJoinDrop (rezz mempty) subRefl) σ)

shrinkTelescopicEq : telescopicEq α β → ShrinkSubst α α' → telescopicEq α' β
shrinkTelescopicEq ΔEq rσ = TelescopeEq.shrinkCompact (rezz _) ΔEq rσ

---------------------------------------------------------------------------------------------------
                          {- PART THREE : Unification Step By Step -}
---------------------------------------------------------------------------------------------------

data UnificationStep (Γ : Context α) : telescopicEq α β → Context α' → telescopicEq α' β' → Set

syntax UnificationStep Γ ΔEq Γ' ΔEq' = Γ , ΔEq ↣ᵤ Γ' , ΔEq'

data UnificationStep {α = α} Γ where
  SolutionL :
    {e₀ : Name}
    {(⟨ x ⟩ x∈α) : NameIn α}
    (let α' = diff x∈α)
    {u : Term α}
    {A : Type _}
    {ΔEq : TelescopeEq.Compact α  (e₀ ◃ mempty) β}
    (rσ : ShrinkSubst _ _)
    (let  A' = A
          Γ' : Context α'
          Γ' = shrinkContext Γ rσ
          ΔEqN : telescopicEq α β
          ΔEqN = normalizeEq (rezz α) ΔEq ⌈ e₀ ↦ u ◃⌉                   {- normalize the telescopic equality -}
          ΔEq' : telescopicEq α' β
          ΔEq' = shrinkTelescopicEq ΔEqN rσ)                            {- replace e₀ by u -}
    -------------------------------------------------------------------
    → Γ , ⌈ e₀ ↦ TVar (⟨ x ⟩ x∈α) ≟ u ∶ A' ◃ ΔEq ⌉ ↣ᵤ Γ' , ΔEq'


{-
Unification : (Γ : Context α) → telescopicEq α β → (Σ[ α' ∈ Scope Name ] Context α')
Unification Γ EmptyEq = do
  let αbis ⟨ eα ⟩ = rezzScope Γ
  (αbis , subst0 (λ α → Context α) eα Γ)
Unification Γ (TelescopeEq.ExtendEq x u v A ΔEqAux) = {!   !}
-}