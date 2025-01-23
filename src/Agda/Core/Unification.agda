open import Scope

open import Haskell.Prelude hiding (All; s; t; a; coerce)
open import Haskell.Extra.Erase
open import Haskell.Law.Equality renaming (subst to transport)
open import Haskell.Law.Monoid.Def

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Utils
open import Agda.Core.Syntax
open import Agda.Core.Signature
open import Agda.Core.Substitute
open import Agda.Core.Context
open import Agda.Core.ScopeUtils
open import Agda.Core.TCM
open import Agda.Core.TCMInstances

module Agda.Core.Unification
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

opaque
  unfolding Scope
  renamingToSubst : ∀ {@0 α β : Scope Name} → Rezz α → Renaming α β → α ⇒ β
  renamingToSubst (rezz []) _ = ⌈⌉
  renamingToSubst (rezz (Erased x ∷ α)) r =
    let r' : Renaming α _
        r' = λ xp → r (coerce (subBindDrop subRefl) xp) in
    ⌈ x ↦  TVar < r (Zero ⟨ IsZero refl ⟩) > ◃ renamingToSubst (rezz α) r' ⌉

---------------------------------------------------------------------------------------------------
                                   {- PART ONE : Shrinking -}
---------------------------------------------------------------------------------------------------
module Shrinking where
  {- A module where shrinking, an operation to remove some variables of a scope while
    preserving dependancies is defined -}

  private variable
    @0 x : Name
    @0 α β : Scope Name

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
    shrinkContext : Context α → ShrinkSubst α β → Context β
    shrinkContext CtxEmpty RNil = CtxEmpty
    shrinkContext (CtxExtend Γ x a) (RKeep σ) =
      CtxExtend (shrinkContext Γ σ) x (subst (ShrinkSubstToSubst σ) a)
    shrinkContext (CtxExtend Γ x a) (RCons u σ) = shrinkContext Γ σ

  opaque
    unfolding cut
    shrinkFromCut : Rezz α → (xp : x ∈ α) → Term (cutDrop xp) → ShrinkSubst α (cutTake xp <> cutDrop xp)
    shrinkFromCut (rezz (_ ∷  α')) (Zero ⟨ IsZero refl ⟩) u = RCons u (idShrinkSubst (rezz α'))
    shrinkFromCut (rezz (_ ∷ α')) (Suc n ⟨ IsSuc p ⟩) u = RKeep (shrinkFromCut (rezz α') (n ⟨ p ⟩) u)

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
module UnificationStepAndStop where
  private variable
    @0 e₀ x : Name
    @0 α α' β β' : Scope Name
    δ₁ δ₂ : β ⇒ α
    ds : Sort α

  data UnificationStep (Γ : Context α) : TelescopicEq α β → Context α' → TelescopicEq α' β' → Set
  data UnificationStop (Γ : Context α) : TelescopicEq α β → Set
  infix 3 _,_↣ᵤ_,_
  infix 3 _,_↣ᵤ⊥
  _,_↣ᵤ_,_ = UnificationStep
  _,_↣ᵤ⊥ = UnificationStop

  data UnificationStep {α = α} Γ where

    {- remove equalities of the form t = t -}
    Deletion :
      {t : Term α}
      {Ξ : Telescope α (e₀ ◃ β)}
      (let Δ : Telescope α β
           Δ = telescopeDrop (rezz α) Ξ t)                             -- replace e₀ by t in the telescope
      ------------------------------------------------------------
      → Γ , ⌈ e₀ ↦ t ◃ δ₁ ⌉ ≟ ⌈ e₀ ↦ t ◃ δ₂ ⌉ ∶ Ξ ↣ᵤ Γ , δ₁ ≟ δ₂ ∶ Δ

    {- solve equalities of the form x = u when x is a variable -}
    SolutionL :
      {xp : x ∈ α}
      (let α₀ , α₁ = cut xp
           α' = α₁ <> α₀)                                              -- new scope without x
      {u : Term α}
      {u₀ : Term α₀}                                                   -- u₀ is independant from x as x ∉ α₀
      {Ξ : Telescope α (e₀ ◃ β)}
      (let rσ = shrinkFromCut (rezz α) xp u₀                            -- an order preserving substitution to remove x
           Γ' : Context α'
           Γ' = shrinkContext Γ rσ                                     -- new context where x is removed
           ΔEq : TelescopicEq α β
           ΔEq = δ₁ ≟ δ₂ ∶ telescopeDrop (rezz α) Ξ u                  -- replace e₀ by u in the telescopic equality
           ΔEq' : TelescopicEq α' β
           ΔEq' = substTelescopicEq (ShrinkSubstToSubst rσ) ΔEq)       -- replace x by u
      → Just u₀ ≡ strengthen subCutDrop u
      ------------------------------------------------------------
      → Γ , ⌈ e₀ ↦ TVar (⟨ x ⟩ xp) ◃ δ₁ ⌉ ≟ ⌈ e₀ ↦ u ◃ δ₂ ⌉ ∶ Ξ ↣ᵤ Γ' , ΔEq'

    {- solve equalities of the form c i = c j for a constructor c of a datatype d -}
    {- this only work with K -}
    Injectivity :
      {d : NameIn dataScope}                                                     -- the datatype
      (let dt = sigData sig d)                                                   -- representation of the datatype d
      {pSubst : dataParScope d ⇒ α}                                              -- value of the parameters of d
      {iSubst : dataIxScope d ⇒ α}                                               -- value of the indices of d
      {Δe₀ : Telescope (e₀ ◃ α) β}
      ( (⟨ c₀ ⟩ cFromd) : NameIn (dataConstructorScope dt))                      -- c is a constructor of dt
      (let cFromCon , con = dataConstructors dt (⟨ c₀ ⟩ cFromd)
           c = (⟨ c₀ ⟩ cFromCon)                                                 -- c is a constructor of a datatype
           γ : Scope Name
           γ = fieldScope c)                                                     -- name of the arguments of c
      {σ₁ σ₂ : γ ⇒ α}
      (let Σ : Telescope α γ
           Σ = subst pSubst (conTelescope con)                                   -- type of the arguments of c
           σe : γ ⇒ (~ γ <> α)
           σe = weaken (subJoinHere (rezz _) subRefl) (revIdSubst (rezz γ))      -- names of the new equalities to replace e₀
           τ₀ : [ e₀ ] ⇒ (~ γ <> α)
           τ₀ = subst0 (λ ξ₀ → ξ₀ ⇒ (~ γ <> α)) (rightIdentity _) ⌈ e₀ ↦ TCon c σe ◃⌉
           τ : (e₀ ◃ α) ⇒ (~ γ <> α)
           τ = concatSubst τ₀ (weaken (subJoinDrop (rezz _) subRefl) (idSubst (rezz α)))
           Δγ : Telescope (~ γ <> α) β                                           -- telescope using ~ γ instead of e₀
           Δγ = subst τ Δe₀)
      ------------------------------------------------------------------- ⚠ NOT a rewrite rule ⚠ (c = (⟨ c₀ ⟩ cFromCon))
     → Γ , ⌈ e₀ ↦ TCon c σ₁ ◃ δ₁ ⌉ ≟ ⌈ e₀ ↦ TCon c σ₂ ◃ δ₂ ⌉ ∶ ⌈ e₀ ∶ El ds (TData d pSubst iSubst) ◃ Δe₀ ⌉
        ↣ᵤ Γ , concatSubst σ₁ δ₁ ≟ concatSubst σ₂ δ₂ ∶ addTel Σ Δγ

    {- solve equalities of the form c i = c j for a constructor c of a datatype d -}
    InjectivityDep :
      {- from β = ixs <> (e₀ ◃ β₀) to β' = γ <> β₀ -}
      {β₀ : Scope Name}
      {δ₁ δ₂ : β₀ ⇒ α}
      {d : NameIn dataScope}                                                     -- the datatype
      (let dt = sigData sig d
           pars = dataParScope d
           ixs = dataIxScope d)
      {ds : Sort (~ ixs <> α)}
      {pSubst : pars ⇒ α}                                                        -- value of the parameters of d
      {iSubst₁ iSubst₂ : ixs ⇒ α}                                                -- value of the indices of d
      {Δe₀ixs : Telescope (e₀ ◃ (~ ixs <>  α)) β₀}
      { (⟨ c₀ ⟩ cFromd) : NameIn (dataConstructorScope dt)}                      -- c is a constructor of dt
      (let cFromCon , con = dataConstructors dt (⟨ c₀ ⟩ cFromd)
           c = (⟨ c₀ ⟩ cFromCon)                                                 -- c is a constructor of a datatype
           γ : Scope Name
           γ = fieldScope c)                                                     -- name of the arguments of c
      {σ₁ σ₂ : γ ⇒ α}
      (let Σ : Telescope α γ
           Σ = subst pSubst (conTelescope con)                                   -- type of the arguments of c

           iTel : Telescope α ixs
           iTel = subst pSubst (dataIndexTel dt)

           iSubste : ixs ⇒ (~ ixs <> α)
           iSubste = weakenSubst (subJoinHere (rezz _) subRefl) (revIdSubst (rezz ixs))
           weakenα : α ⇒ (~ ixs <> α)
           weakenα = weaken (subJoinDrop (rezz _) subRefl) (idSubst (rezz α))

           σe : γ ⇒ (~ γ <> α)
           σe = weaken (subJoinHere (rezz _) subRefl) (revIdSubst (rezz γ))
           τ₀ : [ e₀ ] ⇒ (~ γ <> α)
           τ₀ = subst0 (λ ξ₀ → ξ₀ ⇒ (~ γ <> α)) (rightIdentity _) ⌈ e₀ ↦ TCon c σe ◃⌉
           τ₁ : ~ ixs ⇒ (~ γ <> α)
           τ₁ = subst (subst (liftSubst (rezz _) pSubst) (conIndices con)) (revIdSubst' (rezz _))
           τ₂ : α ⇒ (~ γ <> α)
           τ₂ = weaken (subJoinDrop (rezz _) subRefl) (idSubst (rezz α))
           τ : (e₀ ◃ (~ ixs <>  α)) ⇒ (~ γ <> α)
           τ = concatSubst τ₀ (concatSubst τ₁ τ₂)
           Δγ : Telescope (~ γ <> α) β₀
           Δγ = subst τ Δe₀ixs)
     ------------------------------------------------------------------- ⚠ NOT a rewrite rule ⚠
     → Γ , concatSubst iSubst₁ ⌈ e₀ ↦ TCon c σ₁ ◃ δ₁ ⌉ ≟ concatSubst iSubst₂ ⌈ e₀ ↦ TCon c σ₂ ◃ δ₂ ⌉
           ∶ addTel iTel ⌈ e₀ ∶ El ds (TData d (subst weakenα pSubst) iSubste) ◃ Δe₀ixs ⌉
       ↣ᵤ Γ , concatSubst σ₁ δ₁ ≟ concatSubst σ₂ δ₂ ∶ addTel Σ Δγ
    {- TODO: replace Injectivity and InjectivityDep by better rule from article proof relevant Unification (2018) J. Cockx & D. Devriese -}
    {- if possible change definition of constructors and datatypes to make Injectivity a rewrite rule -}
  {- End of UnificationStep -}

  data InSubst (t : Term β) : α ⇒ β → Set
  data InSubst {β = β} t where
    DirectInSubst :
      {σ : α ⇒ β}
      → InSubst t ⌈ x ↦ t ◃ σ ⌉
    RecInSubst :
      {σ : α ⇒ β}
      {u : Term β}
      → InSubst t σ
      → InSubst t ⌈ x ↦ u ◃ σ ⌉

  data CycleProof (x : NameIn α) : Term α → Set
  data CycleProof {α = α} x where
    BasicCycle :
      {c : NameIn conScope}
      {σ : fieldScope c ⇒ α}
      → InSubst (TVar x) σ
      → CycleProof x (TCon c σ)
    SubCycle :
      {u v : Term α}
      {c : NameIn conScope}
      {σ : fieldScope c ⇒ α}
      → CycleProof x v
      → InSubst v σ
      → CycleProof x (TCon c σ)

  data UnificationStop {α = α} Γ where
    Conflict :
      {nameC nameC' : Name}
      {proofC : nameC ∈ conScope}
      {proofC' : nameC' ∈ conScope}
      (let c = ⟨ nameC ⟩ proofC
           c' = ⟨ nameC' ⟩ proofC')
      {σ₁ : fieldScope c ⇒ α}
      {σ₂ : fieldScope c' ⇒ α}
      {Ξ : Telescope α (e₀ ◃ β)}
      → nameC ≠ nameC'
      ------------------------------------------------------------
      → Γ , ⌈ e₀ ↦ TCon c σ₁ ◃ δ₁ ⌉ ≟ ⌈ e₀ ↦ TCon c' σ₂ ◃ δ₂ ⌉ ∶ Ξ ↣ᵤ⊥
    {- cycle right now isn't as strict as it should be to correspond to the
       proof where pattern matching is reduced to eliminator in Jesper Cockx thesis
       it would be nice to rewrite it
       cycle can go through a non inductive argument position a constructor
      (no proof that it can happen but no proof that it cannot) -}
    CycleL :
      {x : NameIn α}
      (u : Term α)
      {Ξ : Telescope α (e₀ ◃ β)}
      → CycleProof x u
      ------------------------------------------------------------
      → Γ , ⌈ e₀ ↦ TVar x ◃ δ₁ ⌉ ≟ ⌈ e₀ ↦ u ◃ δ₂ ⌉ ∶ Ξ ↣ᵤ⊥
    CycleR :
      {x : NameIn α}
      (u : Term α)
      {Ξ : Telescope α (e₀ ◃ β)}
      → CycleProof x u
      ------------------------------------------------------------
      → Γ , ⌈ e₀ ↦ u ◃ δ₂ ⌉ ≟ ⌈ e₀ ↦ TVar x ◃ δ₁ ⌉ ∶ Ξ ↣ᵤ⊥
  {- End of UnificationStop -}

{- End of module UnificationStepAndStop -}
open UnificationStepAndStop

---------------------------------------------------------------------------------------------------
                            {- PART FOUR : Context reordering -}
---------------------------------------------------------------------------------------------------
module Swap where
  private variable
    @0 x y : Name
    @0 α : Scope Name

  private opaque
    unfolding Scope
    swapTwoLast : Context (x ◃ y ◃ α) → Maybe (Context (y ◃ x ◃ α))
    swapTwoLast (CtxExtend (CtxExtend Γ y ay) x ax) = do
      ax' ← strengthen (subBindDrop subRefl) ax
      let ay' = weaken (subBindDrop subRefl) ay
      return ((Γ , x ∶ ax' ) , y ∶ ay')


    {- Idea of swapHighest (x, z, Γ) y:
        - terminaison condition : you swap x and y or fail
        - case 1: if you can swap the two first vars of (x, z, Γ) then
          do it and let Γ1Aux be the result of a recursive call on (x, Γ)
          return (z, Γ1Aux)
        - case 2: if case 1 fails then let Γ' be the result of the
          recursive call on (z, Γ) and return swapHighest (x, Γ') y
      (recursion terminates because the depth of y in the contexts
      used in recursive calls is decreasing.) -}
    swapHighest : {{fl : Fuel}} → Context (x ◃ α) → ((⟨ y ⟩ yp) : NameIn α)
      → TCM (Σ0 _ λ α' → Context α' × Renaming (x ◃ α) α')
    swapHighest (CtxExtend (CtxExtend Γ0 y ay) x ax) (⟨ y ⟩ (Zero ⟨ IsZero refl ⟩)) = do
      Γ' ← liftMaybe (swapTwoLast (CtxExtend (CtxExtend Γ0 y ay) x ax)) "Not swapable"
      let σ : Renaming (x ◃ y ◃ α) (y ◃ x ◃ α)
          σ = (λ zInx◃y◃α → inBindCase zInx◃y◃α
                            (λ where refl → inThere inHere)
                            (λ zIny◃α → inBindCase zIny◃α
                                        (λ where refl → inHere)
                                        (λ zInα → inThere (inThere zInα))))
      return < Γ' , σ >
    swapHighest  {x = x} {α = Erased z ∷ α} {{More {{fl}}}} (CtxExtend (CtxExtend Γ0 z az) x ax) (⟨ y ⟩ (Suc value ⟨ IsSuc proof ⟩)) =
      let Γ : Context (x ◃ z ◃ α)
          Γ = (CtxExtend (CtxExtend Γ0 z az) x ax)
          yInα : y ∈ α
          yInα = value ⟨ proof ⟩ in
      let areTheTwoLastVarsSwapable = do
        (CtxExtend Γ₁ .z az') ← liftMaybe (swapTwoLast Γ) "Not swapable"
        ⟨ α₀' ⟩ (Γ₀' , σ₀ ) ← swapHighest {{fl}} Γ₁  < yInα >
        -- σ₀ : Renaming (x ◃ α) α₀'
        let σ : Renaming (x ◃ z ◃ α) (z ◃ α₀')
            σ = (λ wInx◃z◃α → inBindCase wInx◃z◃α
                            (λ where refl → inThere (σ₀ inHere))
                            (λ wInz◃α → inBindCase wInz◃α
                                        (λ where refl → inHere)
                                        (λ zInα → inThere (σ₀ (inThere zInα)))))
            az' : Type α₀'
            az' = subst (renamingToSubst (rezzScope Γ₁) σ₀) (weaken (subBindDrop subRefl) az)
            res1 : Σ0 _ λ α' → Context α' × Renaming (x ◃ z ◃ α) α'
            res1 = < CtxExtend Γ₀' z az' , σ >
        return res1 in
      let otherCase = do
        ⟨ γ₀ ⟩ (Δ₀ , τ₀) ← swapHighest {{More {{fl}}}} (CtxExtend Γ0 z az) < yInα >
        -- τ₀ : Renaming (z ◃ α) γ₀
        let ax' : Type γ₀
            ax' = subst (renamingToSubst (rezzScope (CtxExtend Γ0 z az)) τ₀) ax
            σ₁ : Renaming (x ◃ z ◃ α) (x ◃ γ₀)
            σ₁ = (λ wInx◃z◃α → inBindCase wInx◃z◃α
                              (λ where refl → inHere)
                              (λ wInz◃α → inThere (τ₀ wInz◃α)))
        ⟨ α' ⟩ (Γ' , σ₂) ← swapHighest {{fl}} (CtxExtend Δ₀ x ax') < τ₀ (inThere yInα) >
        -- σ₂ : Renaming (x ◃ α₀') α'
        let res2 : Σ0 _ λ α' → Context α' × Renaming (x ◃ z ◃ α) α'
            res2 = < Γ' , σ₂ ∘ σ₁ >
        return res2 in
      caseTCM otherCase (λ x → x) areTheTwoLastVarsSwapable
    swapHighest {{None}} _ _ = tcError "not enough fuel to swap a variables in a context"

 {-
    swap : Context α → (x y : NameIn α) → TCM (Σ0 _ λ α' → Context α' × α ⇒ α')
    swap _ (⟨ x ⟩ (Zero ⟨ _ ⟩)) (⟨ y ⟩ (Zero ⟨ _ ⟩)) =
      tcError "cannot swap a variable with itself"
    swap Γ (⟨ x ⟩ (Zero ⟨ IsZero refl ⟩)) (⟨ y ⟩ (Suc value ⟨ IsSuc proof ⟩)) = do
      (I {{fl}}) ← tcmFuel
      ⟨ _ ⟩ (Γ' , _ , σ) ← swapHighest {{fl}} Γ (⟨ y ⟩ (value ⟨ proof ⟩))
      return < Γ' , σ >
    swap _ (⟨ x ⟩ (Suc vx ⟨ px ⟩)) (⟨ y ⟩ (Zero ⟨ IsZero refl ⟩)) =
      tcError "variable in the wrong order (already swaped)"
    swap _ (⟨ x ⟩ (Suc Zero ⟨ _ ⟩)) (⟨ y ⟩ (Suc Zero ⟨ _ ⟩)) =
      tcError "cannot swap a variable with itself"
    swap _ (⟨ x ⟩ (Suc (Suc _) ⟨ _ ⟩)) (⟨ y ⟩ (Suc Zero ⟨ _ ⟩)) =
      tcError "variable in the wrong order (already swaped)"
    swap (CtxExtend Γ z az) (⟨ x ⟩ (Suc vx ⟨ IsSuc px ⟩)) (⟨ y ⟩ (Suc (Suc vy) ⟨ IsSuc (IsSuc py) ⟩)) = do
      ⟨ _ ⟩ (Γ0' , σ) ← swap Γ (⟨ x ⟩ (vx ⟨ px ⟩)) (⟨ y ⟩ ((Suc vy) ⟨ IsSuc py ⟩))
      return < CtxExtend Γ0' z (subst σ az), ⌈ z ↦ TVar (⟨ z ⟩ inHere) ◃ weaken (subBindDrop subRefl) σ ⌉ >

    swapUnsafe : Context α → (x y : NameIn α) → TCM (Σ0 _ λ α' → Context α' × α ⇒ α')
    swapUnsafe _ (⟨ x ⟩ (Zero ⟨ _ ⟩)) (⟨ y ⟩ (Zero ⟨ _ ⟩)) =
      tcError "cannot swap a variable with itself"
    swapUnsafe Γ (⟨ x ⟩ (Zero ⟨ IsZero refl ⟩)) (⟨ y ⟩ (Suc value ⟨ IsSuc proof ⟩)) = do
      (I {{fl}}) ← tcmFuel
      ⟨ _ ⟩ (Γ' , _ , σ) ← swapHighest {{fl}} Γ (⟨ y ⟩ (value ⟨ proof ⟩))
      return < Γ' , σ >
    swapUnsafe Γ (⟨ x ⟩ (Suc vx ⟨ px ⟩)) (⟨ y ⟩ (Zero ⟨ IsZero refl ⟩)) = do
      return < Γ , idSubst (rezzScope Γ) >
    swapUnsafe _ (⟨ x ⟩ (Suc Zero ⟨ _ ⟩)) (⟨ y ⟩ (Suc Zero ⟨ _ ⟩)) =
      tcError "cannot swap a variable with itself"
    swapUnsafe Γ (⟨ x ⟩ (Suc (Suc _) ⟨ _ ⟩)) (⟨ y ⟩ (Suc Zero ⟨ _ ⟩)) = do
      return < Γ  , idSubst (rezzScope Γ) >
    swapUnsafe (CtxExtend Γ z az) (⟨ x ⟩ (Suc vx ⟨ IsSuc px ⟩)) (⟨ y ⟩ (Suc (Suc vy) ⟨ IsSuc (IsSuc py) ⟩)) = do
      ⟨ _ ⟩ (Γ0' , σ) ← swapUnsafe Γ (⟨ x ⟩ (vx ⟨ px ⟩)) (⟨ y ⟩ ((Suc vy) ⟨ IsSuc py ⟩))
      return < CtxExtend Γ0' z (subst σ az), ⌈ z ↦ TVar (⟨ z ⟩ inHere) ◃ weaken (subBindDrop subRefl) σ ⌉ >


-}
  -- swapVarList : Context α → (x : NameIn α) → List (NameIn α) → TCM (Σ0 _ λ α' → Context α' × α ⇒ α')
  -- swapVarList Γ (⟨ x ⟩ xp) ((⟨ y ⟩ yp) ∷ l) = do
  --   ⟨ _ ⟩ (Γ0' , σ0) ← swapUnsafe Γ (⟨ x ⟩ xp) (⟨ y ⟩ yp)
  --   ⟨ _ ⟩ (Γ' , σ) ← swapVarList Γ0' (⟨ x ⟩ {!   !}) {!   !} -- have to apply σ0 on xp and l
  --   return < Γ' , (subst σ σ0) >
  -- swapVarList Γ x [] = MkTCM (λ _ → Right < Γ , idSubst (rezzScope Γ) >)

  -- swapVarTerm : Context α → ((⟨ x ⟩ xp) : NameIn α) → (u : Term α)
  --     → TCM (Σ0 _ λ α' → Context α' ×
  --       (Σ[ xp ∈ (x ∈ α')] (Σ[ σ ∈ α ⇒ α' ] (Σ[ u₀ ∈ Term (cutDrop xp) ]
  --         Just u₀ ≡ strengthen subCutDrop (subst σ u)))))
  -- swapVarTerm Γ (⟨ x ⟩ xp) u = {!   !}
{- End of module Swap -}
open Swap
   