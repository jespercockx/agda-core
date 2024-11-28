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
open import Agda.Core.ScopeUtils
open Cut

module Agda.Core.Unification
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

---------------------------------------------------------------------------------------------------
                                   {- PART ONE : Shrinking -}
---------------------------------------------------------------------------------------------------
module Shrinking where
  {- A module where shrinking, an operation to remove some variables of a scope while
    preserving dependancies is defined -}

  private variable
    @0 x : Name
    @0 α α' β β' : Scope Name

  data ShrinkSubst : (@0 α β : Scope Name) → Set where
    RNil  : ShrinkSubst mempty mempty
    RKeep : ShrinkSubst α β → ShrinkSubst (x ◃ α) (x ◃ β)
    RCons : Term β → ShrinkSubst α β → ShrinkSubst (x ◃ α) β
  {-# COMPILE AGDA2HS ShrinkSubst deriving Show #-}

  opaque
    unfolding Scope
    idShrinkSubst : Rezz α → ShrinkSubst α α
    idShrinkSubst (rezz []) = RNil
    idShrinkSubst (rezz (Erased x ∷ α)) = RKeep (idShrinkSubst (rezz α))


  ShrinkSubstToSubst : ShrinkSubst α β → α ⇒ β
  ShrinkSubstToSubst RNil = ⌈⌉
  ShrinkSubstToSubst (RKeep {x = x} σ) =
    ⌈ x ↦ TVar (⟨ x ⟩ inHere) ◃ weaken (subBindDrop subRefl) (ShrinkSubstToSubst σ) ⌉
  ShrinkSubstToSubst (RCons {x = x} u σ) = ⌈ x ↦ u ◃ ShrinkSubstToSubst σ ⌉

  ShrinkSubstToSub : ShrinkSubst α β → β ⊆ α
  ShrinkSubstToSub RNil = subEmpty
  ShrinkSubstToSub (RKeep {x = x} σ) = subBindKeep (ShrinkSubstToSub σ)
  ShrinkSubstToSub (RCons {x = x} u σ) = subBindDrop (ShrinkSubstToSub σ)

  opaque
    unfolding Scope
    shrinkContext : Context α → ShrinkSubst α α' → Context α'
    shrinkContext CtxEmpty RNil = CtxEmpty
    shrinkContext (CtxExtend Γ x a) (RKeep σ) =
      CtxExtend (shrinkContext Γ σ) x (subst (ShrinkSubstToSubst σ) a)
    shrinkContext (CtxExtend Γ x a) (RCons u σ) = shrinkContext Γ σ

  opaque
    unfolding Sub Split cut
    shrinkFromCut : Rezz α → (x : NameIn α) → Term (cutDrop x) → ShrinkSubst α (cutTake x <> cutDrop x)
    shrinkFromCut _ (⟨ x ⟩ ⟨ _ ⟩ EmptyR) u = RCons u RNil
    shrinkFromCut (rezz (Erased .x ∷  α')) (⟨ x ⟩ ⟨ _ ⟩ ConsL .x p) u = RCons u (idShrinkSubst (rezz α'))
    shrinkFromCut (rezz (_ ∷ α')) (⟨ x ⟩ ⟨ _ ⟩ ConsR y p) u = RKeep (shrinkFromCut (rezz α') (⟨ x ⟩ ⟨ _ ⟩ p) u)

{- End of module Shrinking -}
open Shrinking

---------------------------------------------------------------------------------------------------
                        {- PART TWO : Definition of telescopic equality -}
---------------------------------------------------------------------------------------------------
module TelescopeEq where
  {- A module where :
    - two equivalent versions of the telescopic equality are defined
    - auxiliary datatypes are defined for the two telescopic equality
    - equivalence between the auxiliary datatypes for telescopic equality is proved
    - some transport and substitution auxiliary functions for telescopic equality are implemented
   Read it if you want to understand the structure behind telescopic equality.
  -}

  private variable
    @0 x : Name
    @0 α α₀  α' β β' : Scope Name

  ---------------------------------------------------------------------------------------------------
  {- Expanded version of telescopic equality, where both parts of the equality are already constructed -}
  record TelescopicEq (@0 α β : Scope Name) : Set where
    constructor TelEq
    field
      left : β ⇒ α
      right : β ⇒ α
      telescope : Telescope α β

  infixr 6 _≟_∶_
  pattern _≟_∶_ δ₁ δ₂ Δ = TelEq δ₁ δ₂ Δ

  ---------------------------------------------------------------------------------------------------
  {- Compact version of telescopic equality, where both parts of the equality are constructed step by step -}
  data Compact (@0 α₀ : Scope Name) : (@0 α β : Scope Name) → Set where
    EmptyEq : Compact α₀ α mempty
    ExtendEq : {@0 β : Scope Name} (@0 x : Name)
      (u v : Term α₀) (A : Type (α <> α₀))
      → Compact α₀ (x ◃ α) β
      → Compact α₀ α (x ◃ β)

  telescopicEq' : (@0 α β : Scope Name) → Set
  telescopicEq' α β = Compact α mempty β

  ---------------------------------------------------------------------------------------------------
  {- auxiliary datatype for telescopicEq as independant scopes are needed
     to go from one representation to the other -}
  private
    record Expanded (@0 α₀ α β : Scope Name) : Set where
      constructor TelExp
      field
        left : β ⇒ α₀
        right : β ⇒ α₀
        telescope : Telescope (α <> α₀) β

  ---------------------------------------------------------------------------------------------------
  {- definition of an equivalence -}
  private opaque
    unfolding Scope
    {- Functions to go from one auxiliary datatype to the other -}
    compactToExpanded : Compact α₀ α β → Expanded α₀ α β
    compactToExpanded EmptyEq = TelExp ⌈⌉ ⌈⌉ EmptyTel
    compactToExpanded (ExtendEq x u v a ΔEq) = do
      let TelExp δ₁ δ₂ Δ = compactToExpanded ΔEq
      TelExp ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ a ◃ Δ ⌉

    expandedToCompact : Expanded α₀ α β → Compact α₀ α β
    expandedToCompact (TelExp ⌈⌉ ⌈⌉ EmptyTel) = EmptyEq
    expandedToCompact (TelExp ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ a ◃ Δ ⌉) = do
      let ΔEq = expandedToCompact (TelExp δ₁ δ₂ Δ)
      ExtendEq x u v a ΔEq

    {- The functions above form an equivalence -}
    equivLeft : (ΔEq : Compact α₀ α β)
      → expandedToCompact (compactToExpanded ΔEq) ≡ ΔEq
    equivLeft EmptyEq = refl
    equivLeft (ExtendEq x u v a ΔEq) = do
      let eH = equivLeft ΔEq
      cong (λ ΔEq → ExtendEq x u v a ΔEq) eH

    equivRight : (ΔEq' : Expanded α₀ α β)
      → compactToExpanded (expandedToCompact ΔEq') ≡ ΔEq'
    equivRight (TelExp ⌈⌉ ⌈⌉ ⌈⌉) = refl
    equivRight (TelExp ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ a ◃ Δ ⌉) = do
      let eH = equivRight (TelExp δ₁ δ₂ Δ)
      cong (λ (TelExp δ₁ δ₂ Δ) → TelExp ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ a ◃ Δ ⌉) eH

    equivalenceAux : Equivalence (Compact α₀ α β) (Expanded α₀ α β)
    equivalenceAux = Equiv compactToExpanded expandedToCompact equivLeft equivRight

    telescopicEq'ToEq : telescopicEq' α β → TelescopicEq α β
    telescopicEq'ToEq ΔEq' = do
      let TelExp σ₁ σ₂ Δ = compactToExpanded ΔEq'
      TelEq σ₁ σ₂ Δ

    telescopicEqToEq' : TelescopicEq α β → telescopicEq' α β
    telescopicEqToEq' (TelEq σ₁ σ₂ Δ) = expandedToCompact (TelExp σ₁ σ₂ Δ)

    equivLeftTelEq : (ΔEq' : telescopicEq' α β) → telescopicEqToEq' (telescopicEq'ToEq ΔEq') ≡ ΔEq'
    equivLeftTelEq EmptyEq = refl
    equivLeftTelEq (ExtendEq x u v a ΔEq) = do
      let eH = equivLeft ΔEq
      cong (λ ΔEq → ExtendEq x u v a ΔEq) eH

    equivRightTelEq : (ΔEq : TelescopicEq α β) → telescopicEq'ToEq (telescopicEqToEq' ΔEq) ≡ ΔEq
    equivRightTelEq (TelEq ⌈⌉ ⌈⌉ ⌈⌉) = refl
    equivRightTelEq (TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ a ◃ Δ ⌉) = do
      let eH = equivRight (TelExp δ₁ δ₂ Δ)
      cong (λ (TelExp δ₁ δ₂ Δ) → TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ ⌈ x ∶ a ◃ Δ ⌉) eH

  equivalenceTelEq : {α β : Scope Name} → Equivalence (telescopicEq' α β) (TelescopicEq α β)
  equivalenceTelEq = Equiv telescopicEq'ToEq telescopicEqToEq' equivLeftTelEq equivRightTelEq

  ---------------------------------------------------------------------------------------------------
  {- helpful functions -}

  substTelescopicEq : (α₀ ⇒ α) → TelescopicEq α₀ β → TelescopicEq α β
  substTelescopicEq σ (TelEq δ₁ δ₂ Δ) = TelEq (subst σ δ₁) (subst σ δ₂) (subst σ Δ)
  {-# COMPILE AGDA2HS substTelescopicEq #-}

  instance
    iSubstTelescopicEq : Substitute (λ α → TelescopicEq α β)
    iSubstTelescopicEq .subst = substTelescopicEq
  {-# COMPILE AGDA2HS iSubstTelescopicEq #-}

  opaque
    unfolding Scope
    telescopeDrop : Rezz α → Telescope α (x ◃ β) → Term α → Telescope α β
    telescopeDrop αRun ⌈ x ∶ a ◃ Δ ⌉ w =
      subst (concatSubst ⌈ x ↦ w ◃⌉ (idSubst αRun)) Δ

    telescopicEqDrop : Rezz α → TelescopicEq α (x ◃ β) → Term α → TelescopicEq α β
    telescopicEqDrop αRun (TelEq ⌈ x ↦ u ◃ δ₁ ⌉ ⌈ x ↦ v ◃ δ₂ ⌉ Δ) w = TelEq δ₁ δ₂ (telescopeDrop αRun Δ w)

{- End of module TelescopeEq -}
open TelescopeEq

---------------------------------------------------------------------------------------------------
                          {- PART THREE : Unification Step By Step -}
---------------------------------------------------------------------------------------------------
private variable
  @0 e₀ : Name
  @0 α α' β β' : Scope Name

data UnificationStep (Γ : Context α) : TelescopicEq α β → Context α' → TelescopicEq α' β' → Set
infix 3 _,_↣ᵤ_,_
_,_↣ᵤ_,_ = UnificationStep

data UnificationStep {α = α} Γ where
  Deletion :
    {t : Term α}
    {δ₁ δ₂ : β ⇒ α}
    {Ξ : Telescope α (e₀ ◃ β)}
    (let Δ : Telescope α β
         Δ = telescopeDrop (rezz α) Ξ t)                                       -- reduce the telescope
    ------------------------------------------------------------
    → Γ , ⌈ e₀ ↦ t ◃ δ₁ ⌉ ≟ ⌈ e₀ ↦ t ◃ δ₂ ⌉ ∶ Ξ ↣ᵤ Γ , δ₁ ≟ δ₂ ∶ Δ

  SolutionL :
    {x : NameIn α}
    (let α₀ , α₁ = cut x
         α' = α₁ <> α₀)                                                        -- new scope without x
    (u₀ : Term α₀)
    {δ₁ δ₂ : β ⇒ α}
    {a : Type α}
    {Ξ : Telescope α (e₀ ◃ β)}
    (let rσ = shrinkFromCut (rezz α) x u₀
         u : Term α
         u  = weaken subCutDrop u₀
         Γ' : Context α'
         Γ' = shrinkContext Γ rσ                                               -- new context where x is removed
         ΔEq : TelescopicEq α β
         ΔEq = δ₁ ≟ δ₂ ∶ telescopeDrop (rezz α) Ξ u                            -- reduce the telescopic equality
         ΔEq' : TelescopicEq α' β
         ΔEq' = substTelescopicEq (ShrinkSubstToSubst rσ) ΔEq)                 -- replace e₀ by u
    ------------------------------------------------------------               -- this is NOT a rewrite rule
    → Γ , ⌈ e₀ ↦ TVar x ◃ δ₁ ⌉ ≟ ⌈ e₀ ↦ u ◃ δ₂ ⌉ ∶ Ξ ↣ᵤ Γ' , ΔEq'

  Injectivity :
    {δ₁ δ₂ : β ⇒ α}
    {d : NameIn dataScope}
    {ds : Sort α}
    (let dt = sigData sig d
         pars = dataParScope d
         ixs = dataIxScope d)
    {pSubst : pars ⇒ α}
    {iSubst : ixs ⇒ α}
    {a : Type α}
    {Δ : Telescope (e₀ ◃ α) β}
    { (⟨ c₀ ⟩ cFromd) : NameIn (dataConstructorScope dt)}
    (let cFromCon , con = dataConstructors dt (⟨ c₀ ⟩ cFromd)
         c = (⟨ c₀ ⟩ cFromCon)
         γ : Scope Name
         γ = fieldScope c)
    {σ₁ σ₂ : γ ⇒ α}
    (let Σ : Telescope α γ
         Σ = subst pSubst (conTelescope con)
         s : α ⊆ (~ γ <> α)
         s = subJoinDrop (rezz (~ γ)) subRefl
         Ξ : Telescope α (e₀ ◃ β)
         Ξ = ⌈ e₀ ∶ El ds (TData d pSubst iSubst) ◃ Δ ⌉
         Ξw : Telescope (~ γ <> α) (e₀ ◃ β)
         Ξw = weakenTel s Ξ
         s' : (~ γ) ⊆ (~ γ <> α)
         s' = subJoinHere (rezz (~ γ)) subRefl
         σe : γ ⇒ (~ γ <> α)
         σe = weaken s' (revIdSubst (rezz γ))
         Δw : Telescope (~ γ <> α) β
         Δw = telescopeDrop (rezz _) Ξw (TCon c σe)
         ω₁ : (γ <> β) ⇒ α
         ω₁ = concatSubst σ₁ δ₁
         ω₂ : (γ <> β) ⇒ α
         ω₂ = concatSubst σ₂ δ₂
         Ω : Telescope α (γ <> β)
         Ω = addTel Σ Δw
         ΩEq : TelescopicEq α (γ <> β)
         ΩEq = ω₁ ≟ ω₂ ∶ Ω)
    -------------------------------------------------------------------
    → Γ , ⌈ e₀ ↦ TCon c σ₁ ◃ δ₁ ⌉ ≟ ⌈ e₀ ↦ TCon c σ₂ ◃ δ₂ ⌉ ∶ ⌈ e₀ ∶ El ds (TData d pSubst iSubst) ◃ Δ ⌉
      ↣ᵤ Γ , ΩEq