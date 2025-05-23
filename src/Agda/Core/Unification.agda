open import Haskell.Prelude hiding (All; s; t; a; coerce)
open import Haskell.Extra.Erase
open import Haskell.Law.Equality renaming (subst to transport)
open import Haskell.Law.Semigroup.Def using (associativity)

open import Agda.Core.Name
open import Agda.Core.Utils
open import Agda.Core.Syntax
open import Agda.Core.Syntax.Strengthening

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
    @0 α β : Scope Name

  data ShrinkSubst : (@0 α β : Scope Name) → Set where
    RNil  : ShrinkSubst mempty mempty
    RKeep : ShrinkSubst α β → ShrinkSubst  (α ▸ x)  (β ▸ x)
    RCons : Term β → ShrinkSubst α β → ShrinkSubst  (α ▸ x) β
  {-# COMPILE AGDA2HS ShrinkSubst deriving Show #-}

  opaque
    unfolding Scope
    idShrinkSubst : Rezz α → ShrinkSubst α α
    idShrinkSubst (rezz []) = RNil
    idShrinkSubst (rezz (Erased x ∷ α)) = RKeep (idShrinkSubst (rezz α))


  ShrinkSubstToSubst : ShrinkSubst α β → α ⇒ β
  ShrinkSubstToSubst RNil = ⌈⌉
  ShrinkSubstToSubst (RKeep {x = x} σ) =
    weaken (subBindDrop subRefl) (ShrinkSubstToSubst σ) ▹ x ↦ TVar (⟨ x ⟩ inHere)
  ShrinkSubstToSubst (RCons {x = x} u σ) = ShrinkSubstToSubst σ ▹ x ↦ u
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
    shrinkFromCut : Rezz α → (xp : x ∈ α) → Term (cutDrop xp) → ShrinkSubst α (cutDrop xp <> cutTake xp)
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
    @0 α α₀ : Scope Name
    @0 rβ : RScope Name

  ---------------------------------------------------------------------------------------------------
  {- Expanded version of telescopic equality, where both parts of the equality are already constructed -}
  record TelescopicEq (@0 α : Scope Name) (@0 rβ : RScope Name) : Set where
    constructor TelEq
    field
      left : TermS α rβ
      right : TermS α rβ
      telescope : Telescope α rβ

  infixr 6 _≟_∶_
  pattern _≟_∶_ δ₁ δ₂ Δ = TelEq δ₁ δ₂ Δ

  ---------------------------------------------------------------------------------------------------
  {- Compact version of telescopic equality, where both parts of the equality are constructed step by step -}
  data Compact (@0 α₀ : Scope Name) : (@0 α : Scope Name) (@0 rβ : RScope Name) → Set where
    EmptyEq : Compact α₀ α mempty
    ExtendEq : {@0 rβ : RScope Name} (@0 x : Name)
      (u v : Term α₀) (A : Type (α₀ <> α))
      → Compact α₀  (α ▸ x) rβ
      → Compact α₀ α (x ◂ rβ)

  telescopicEq' : (@0 α : Scope Name) (@0 rβ : RScope Name) → Set
  telescopicEq' α rβ = Compact α mempty rβ

  ---------------------------------------------------------------------------------------------------
  {- auxiliary datatype for telescopicEq as independant scopes are needed
     to go from one representation to the other -}
  private
    record Expanded (@0 α₀ α : Scope Name) (@0 rβ : RScope Name) : Set where
      constructor TelExp
      field
        left : TermS α₀ rβ
        right : TermS α₀ rβ
        telescope : Telescope (α₀ <> α) rβ

  ---------------------------------------------------------------------------------------------------
  {- definition of an equivalence -}
  private opaque
    unfolding Scope RScope
    {- Functions to go from one auxiliary datatype to the other -}
    compactToExpanded : Compact α₀ α rβ → Expanded α₀ α rβ
    compactToExpanded EmptyEq = TelExp ⌈⌉ ⌈⌉ EmptyTel
    compactToExpanded (ExtendEq x u v a ΔEq) = do
      let TelExp δ₁ δ₂ Δ = compactToExpanded ΔEq
      TelExp (x ↦ u ◂ δ₁) (x ↦ v ◂ δ₂) (x ∶ a ◂ Δ)

    expandedToCompact : Expanded α₀ α rβ → Compact α₀ α rβ
    expandedToCompact (TelExp ⌈⌉ ⌈⌉ EmptyTel) = EmptyEq
    expandedToCompact (TelExp (x ↦ u ◂ δ₁) (x ↦ v ◂ δ₂) (x ∶ a ◂ Δ)) = do
      let ΔEq = expandedToCompact (TelExp δ₁ δ₂ Δ)
      ExtendEq x u v a ΔEq

    {- The functions above form an equivalence -}
    equivLeft : (ΔEq : Compact α₀ α rβ)
      → expandedToCompact (compactToExpanded ΔEq) ≡ ΔEq
    equivLeft EmptyEq = refl
    equivLeft (ExtendEq x u v a ΔEq) = do
      let eH = equivLeft ΔEq
      cong (λ ΔEq → ExtendEq x u v a ΔEq) eH

    equivRight : (ΔEq' : Expanded α₀ α rβ)
      → compactToExpanded (expandedToCompact ΔEq') ≡ ΔEq'
    equivRight (TelExp ⌈⌉ ⌈⌉ ⌈⌉) = refl
    equivRight (TelExp (x ↦ u ◂ δ₁) (x ↦ v ◂ δ₂) (x ∶ a ◂ Δ)) = do
      let eH = equivRight (TelExp δ₁ δ₂ Δ)
      cong (λ (TelExp δ₁ δ₂ Δ) → TelExp (x ↦ u ◂ δ₁) (x ↦ v ◂ δ₂) (x ∶ a ◂ Δ)) eH

    equivalenceAux : Equivalence (Compact α₀ α rβ) (Expanded α₀ α rβ)
    equivalenceAux = Equiv compactToExpanded expandedToCompact equivLeft equivRight

    telescopicEq'ToEq : telescopicEq' α rβ → TelescopicEq α rβ
    telescopicEq'ToEq ΔEq' = do
      let TelExp σ₁ σ₂ Δ = compactToExpanded ΔEq'
      TelEq σ₁ σ₂ Δ

    telescopicEqToEq' : TelescopicEq α rβ → telescopicEq' α rβ
    telescopicEqToEq' (TelEq σ₁ σ₂ Δ) = expandedToCompact (TelExp σ₁ σ₂ Δ)

    equivLeftTelEq : (ΔEq' : telescopicEq' α rβ) → telescopicEqToEq' (telescopicEq'ToEq ΔEq') ≡ ΔEq'
    equivLeftTelEq EmptyEq = refl
    equivLeftTelEq (ExtendEq x u v a ΔEq) = do
      let eH = equivLeft ΔEq
      cong (λ ΔEq → ExtendEq x u v a ΔEq) eH

    equivRightTelEq : (ΔEq : TelescopicEq α rβ) → telescopicEq'ToEq (telescopicEqToEq' ΔEq) ≡ ΔEq
    equivRightTelEq (TelEq ⌈⌉ ⌈⌉ ⌈⌉) = refl
    equivRightTelEq (TelEq (x ↦ u ◂ δ₁) (x ↦ v ◂ δ₂) (x ∶ a ◂ Δ)) = do
      let eH = equivRight (TelExp δ₁ δ₂ Δ)
      cong (λ (TelExp δ₁ δ₂ Δ) → TelEq (x ↦ u ◂ δ₁) (x ↦ v ◂ δ₂) (x ∶ a ◂ Δ)) eH

  equivalenceTelEq : {α : Scope Name} {rβ : RScope Name} → Equivalence (telescopicEq' α rβ) (TelescopicEq α rβ)
  equivalenceTelEq = Equiv telescopicEq'ToEq telescopicEqToEq' equivLeftTelEq equivRightTelEq

  ---------------------------------------------------------------------------------------------------
  {- helpful functions -}

  substTelescopicEq : (α₀ ⇒ α) → TelescopicEq α₀ rβ → TelescopicEq α rβ
  substTelescopicEq σ (TelEq δ₁ δ₂ Δ) = TelEq (subst σ δ₁) (subst σ δ₂) (subst σ Δ)
  {-# COMPILE AGDA2HS substTelescopicEq #-}

  instance
    iSubstTelescopicEq : Substitute (λ α → TelescopicEq α rβ)
    iSubstTelescopicEq .subst = substTelescopicEq
  {-# COMPILE AGDA2HS iSubstTelescopicEq #-}

  opaque
    unfolding Scope RScope
    telescopeDrop : Rezz α → Telescope α (x ◂ rβ) → Term α → Telescope α rβ
    telescopeDrop αRun (x ∶ a ◂ Δ) w =
      substTelescope (idSubst αRun ▹ x ↦ w) Δ

    telescopicEqDrop : Rezz α → TelescopicEq α (x ◂ rβ) → Term α → TelescopicEq α rβ
    telescopicEqDrop αRun (TelEq (x ↦ u ◂ δ₁) (x ↦ v ◂ δ₂) Δ) w = TelEq δ₁ δ₂ (telescopeDrop αRun Δ w)

{- End of module TelescopeEq -}
open TelescopeEq public

---------------------------------------------------------------------------------------------------
                          {- PART THREE : Unification Step By Step -}
---------------------------------------------------------------------------------------------------
module UnificationStepAndStop where
  private variable
    @0 e₀ x : Name
    @0 α α' α'' : Scope Name
    @0 rβ rβ' rβ'' : RScope Name
    δ₁ δ₂ : TermS α rβ
    ds : Sort α

  data UnificationStep (Γ : Context α) : TelescopicEq α rβ → Context α' → TelescopicEq α' rβ' → Set
  data UnificationStop (Γ : Context α) : TelescopicEq α rβ → Set
  infix 3 _,_↣ᵤ_,_
  infix 3 _,_↣ᵤ⊥
  _,_↣ᵤ_,_ = UnificationStep
  _,_↣ᵤ⊥ = UnificationStop

  @0 Strengthened : ∀ {@0 α β : Scope Name} → Term β → Term α → Set
  Strengthened {α = α} {β = β} u u₀ = (∃[ p ∈ α ⊆ β ] Just u₀ ≡ strengthen p u)

  data UnificationStep {α = α} Γ where

    {- remove equalities of the form t = t -}
    Deletion :
      {t : Term α}
      {Ξ : Telescope α (e₀ ◂ rβ)}
      (let Δ : Telescope α rβ
           Δ = telescopeDrop (rezz α) Ξ t)                             -- replace e₀ by t in the telescope
      ------------------------------------------------------------
      → Γ , (e₀ ↦ t ◂ δ₁) ≟ (e₀ ↦ t ◂ δ₂) ∶ Ξ ↣ᵤ Γ , δ₁ ≟ δ₂ ∶ Δ

    {- solve equalities of the form x = u when x is a variable -}
    SolutionL :
      {xp : x ∈ α}
      (let α₀ , α₁ = cut xp
           α' = α₀ <> α₁)                                              -- new scope without x
      {u : Term α}
      {u₀ : Term α₀}                                                   -- u₀ is independant from x as x ∉ α₀
      {Ξ : Telescope α (e₀ ◂ rβ)}
      (let rσ = shrinkFromCut (rezz α) xp u₀                            -- an order preserving substitution to remove x
           Γ' : Context α'
           Γ' = shrinkContext Γ rσ                                     -- new context where x is removed
           ΔEq : TelescopicEq α rβ
           ΔEq = δ₁ ≟ δ₂ ∶ telescopeDrop (rezz α) Ξ u                  -- replace e₀ by u in the telescopic equality
           ΔEq' : TelescopicEq α' rβ
           ΔEq' = substTelescopicEq (ShrinkSubstToSubst rσ) ΔEq)       -- replace x by u
      → Strengthened u u₀
      ------------------------------------------------------------
      → Γ , (e₀ ↦ TVar (⟨ x ⟩ xp) ◂ δ₁) ≟ (e₀ ↦ u ◂ δ₂) ∶ Ξ ↣ᵤ Γ' , ΔEq'

    SolutionR :
      {xp : x ∈ α}
      (let α₀ , α₁ = cut xp
           α' = α₀ <> α₁)                                              -- new scope without x
      {u : Term α}
      {u₀ : Term α₀}                                                   -- u₀ is independant from x as x ∉ α₀
      {Ξ : Telescope α (e₀ ◂ rβ)}
      (let rσ = shrinkFromCut (rezz α) xp u₀                            -- an order preserving substitution to remove x
           Γ' : Context α'
           Γ' = shrinkContext Γ rσ                                     -- new context where x is removed
           ΔEq : TelescopicEq α rβ
           ΔEq = δ₁ ≟ δ₂ ∶ telescopeDrop (rezz α) Ξ u                  -- replace e₀ by u in the telescopic equality
           ΔEq' : TelescopicEq α' rβ
           ΔEq' = substTelescopicEq (ShrinkSubstToSubst rσ) ΔEq)       -- replace x by u
      → Strengthened u u₀
      ------------------------------------------------------------
      → Γ , (e₀ ↦ u ◂ δ₁) ≟ (e₀ ↦ TVar (⟨ x ⟩ xp) ◂ δ₂) ∶ Ξ ↣ᵤ Γ' , ΔEq'

    {- solve equalities of the form c i = c j for a constructor c of a datatype d -}
    {- this only work with K -}
    Injectivity :
      {d : NameData}                                                     -- the datatype
      (let dt = sigData sig d)                                                   -- representation of the datatype d
      {pSubst : TermS α (dataParScope d)}                                              -- value of the parameters of d
      {iSubst : TermS α (dataIxScope d)}                                               -- value of the indices of d
      {Δe₀ : Telescope (α ▸ e₀) rβ}
      (c : NameCon d)                      -- c is a constructor of d
      (let con = sigCons sig d c
           rγ : RScope Name
           rγ = fieldScope c)                                                     -- name of the arguments of c
      {σ₁ σ₂ : TermS α rγ}
      (let Σ : Telescope α rγ
           Σ = instConIndTel con pSubst                                   -- type of the arguments of c
           σe : TermS (extScope α rγ) (e₀ ◂ mempty)
           σe = e₀ ↦ TCon c (termSrepeat (rezz rγ)) ◂ ⌈⌉           -- names of the new equalities to replace e₀
           τ₀ : extScope α (e₀ ◂ mempty) ⇒ (extScope α rγ)
           τ₀ = extSubst (substExtScope (rezz rγ) (idSubst (rezz α))) σe
           τ : (α ▸ e₀) ⇒ (extScope α rγ)
           τ = subst0 (λ ψ → ψ ⇒ (extScope α rγ)) (trans extScopeBind extScopeEmpty) τ₀
           Δγ : Telescope (extScope α rγ) rβ                           -- telescope using rγ instead of e₀
           Δγ = substTelescope τ Δe₀)
      -------------------------------------------------------------------
     → Γ , (e₀ ↦ TCon c σ₁ ◂ δ₁) ≟ (e₀ ↦ TCon c σ₂ ◂ δ₂) ∶ (e₀ ∶ dataType d ds pSubst iSubst ◂ Δe₀)
        ↣ᵤ Γ , concatTermS σ₁ δ₁ ≟ concatTermS σ₂ δ₂ ∶ addTel Σ Δγ

    {- solve equalities of the form c i = c j for a constructor c of a datatype d -}
    InjectivityDep :
      {- from β = ixs <> (e₀ ◃ β₀) to β' = γ <> β₀ -}
      {rβ₀ : RScope Name}
      {δ₁ δ₂ : TermS α rβ₀}
      {d : NameData}                                                     -- the datatype
      (let dt = sigData sig d
           pars = dataParScope d
           ixs = dataIxScope d)
      {ds : Sort (extScope α ixs)}
      {pSubst : TermS α pars}                                                    -- value of the parameters of d
      {iSubst₁ iSubst₂ : TermS α ixs}                                            -- value of the indices of d
      {Δe₀ixs : Telescope (extScope α ixs ▸ e₀) rβ₀}
      {c : NameCon d}                      -- c is a constructor of dt
      (let con = sigCons sig d c
           ind : RScope Name
           ind = fieldScope c)                                                     -- name of the arguments of c
      {σ₁ σ₂ : TermS α ind}
      (let Σ : Telescope α ind
           Σ = instConIndTel con pSubst                                    -- type of the arguments of c

           iTel : Telescope α ixs
           iTel = instDataIxTel dt pSubst

           iSubste : TermS (extScope α ixs) ixs
           iSubste = termSrepeat (rezz ixs)
           weakenαixs : α ⇒ (extScope α ixs)
           weakenαixs = substExtScope (rezz ixs) (idSubst (rezz α))

           weakenαind : α ⇒ (extScope α ind)
           weakenαind = substExtScope (rezz ind) (idSubst (rezz α))
           σe : TermS (extScope α ind) (e₀ ◂ mempty)
           σe = e₀ ↦ TCon c (termSrepeat(rezz ind)) ◂ ⌈⌉
           τ₀ : TermS (extScope α ind) ixs
           τ₀ = (instConIx con (weaken (subExtScope (rezz ind) subRefl) pSubst) (termSrepeat(rezz ind)))
           τ₁ : extScope α ixs ⇒ (extScope α ind)
           τ₁ = extSubst {rγ = ixs} weakenαind τ₀
           τ₀ : extScope (extScope α ixs) (e₀ ◂ mempty) ⇒ (extScope α ind)
           τ₀ = extSubst τ₁ σe
           τ  : (extScope α ixs) ▸ e₀ ⇒ (extScope α ind)
           τ = subst0 (λ ψ → ψ ⇒ (extScope α ind)) (trans extScopeBind extScopeEmpty) τ₀
           Δγ : Telescope (extScope α ind) rβ₀
           Δγ = subst τ Δe₀ixs)
     -------------------------------------------------------------------
     → Γ , concatTermS iSubst₁ (e₀ ↦ TCon c σ₁ ◂ δ₁) ≟ concatTermS iSubst₂ (e₀ ↦ TCon c σ₂ ◂ δ₂)
           ∶ addTel iTel (e₀ ∶ dataType d ds (subst weakenαixs pSubst) iSubste ◂ Δe₀ixs)
       ↣ᵤ Γ , concatTermS σ₁ δ₁ ≟ concatTermS σ₂ δ₂ ∶ addTel Σ Δγ
    {- TODO: replace Injectivity and InjectivityDep by better rule from article proof relevant Unification (2018) J. Cockx & D. Devriese -}
  {- End of UnificationStep -}

  data InTermS (t : Term α) : TermS α rβ → Set
  data InTermS {α = α} t where
    DirectInTermS :
      {σ : TermS α rβ}
      → InTermS t (x ↦ t ◂ σ)
    RecInTermS :
      {σ : TermS α rβ}
      {u : Term α}
      → InTermS t σ
      → InTermS t (x ↦ u ◂ σ)

  data CycleProof (x : NameIn α) : Term α → Set
  data CycleProof {α = α} x where
    BasicCycle :
      {d : NameData}
      {c : NameCon d}
      {σ : TermS α (fieldScope c)}
      → InTermS (TVar x) σ
      → CycleProof x (TCon c σ)
    SubCycle :
      {u v : Term α}
      {d : NameData}
      {c : NameCon d}
      {σ : TermS α (fieldScope c)}
      → CycleProof x v
      → InTermS v σ
      → CycleProof x (TCon c σ)

  data UnificationStop {α = α} Γ where
    ConflictData :
      {d d' : NameData}
      {c : NameCon d} {c' : NameCon d'}
      {σ₁ : TermS α (fieldScope c)}
      {σ₂ : TermS α (fieldScope c')}
      {Ξ : Telescope α (e₀ ◂ rβ)}
      → d ≠ d'
      ------------------------------------------------------------
      → Γ , (e₀ ↦ TCon c σ₁ ◂ δ₁) ≟ (e₀ ↦ TCon c' σ₂ ◂ δ₂) ∶ Ξ ↣ᵤ⊥
    ConflictCon :
      {d d' : NameData}
      {c : NameCon d} {c' : NameCon d'}
      {σ₁ : TermS α (fieldScope c)}
      {σ₂ : TermS α (fieldScope c')}
      {Ξ : Telescope α (e₀ ◂ rβ)}
      (e : d ≡ d')
      → c' ≠ transport NameCon e c
      ------------------------------------------------------------
      → Γ , (e₀ ↦ TCon c σ₁ ◂ δ₁) ≟ (e₀ ↦ TCon c' σ₂ ◂ δ₂) ∶ Ξ ↣ᵤ⊥
    {- cycle right now isn't as strict as it should be to correspond to the
       proof where pattern matching is reduced to eliminator in Jesper Cockx thesis
       it would be nice to rewrite it
       cycle can go through a non inductive argument position a constructor
      (no proof that it can happen but no proof that it cannot) -}
    CycleL :
      {x : NameIn α}
      (u : Term α)
      {Ξ : Telescope α (e₀ ◂ rβ)}
      → CycleProof x u
      ------------------------------------------------------------
      → Γ , (e₀ ↦ TVar x ◂ δ₁) ≟ (e₀ ↦ u ◂ δ₂) ∶ Ξ ↣ᵤ⊥
    CycleR :
      {x : NameIn α}
      (u : Term α)
      {Ξ : Telescope α (e₀ ◂ rβ)}
      → CycleProof x u
      ------------------------------------------------------------
      → Γ , (e₀ ↦ u ◂ δ₁) ≟ (e₀ ↦ TVar x ◂ δ₂) ∶ Ξ ↣ᵤ⊥
  {- End of UnificationStop -}


  data UnificationSteps : Context α → TelescopicEq α rβ → Context α' → TelescopicEq α' rβ' → Set where
    StepCons :
      (Γ : Context α) (Γ' : Context α') (Γ'' : Context α'')
      → (Ξ : TelescopicEq α rβ) (Ξ' : TelescopicEq α' rβ') (Ξ'' : TelescopicEq α'' rβ'')
      → UnificationStep Γ Ξ Γ' Ξ' → UnificationSteps Γ' Ξ' Γ'' Ξ''
      → UnificationSteps Γ Ξ Γ'' Ξ''
    StepId : (Γ : Context α) (Ξ : TelescopicEq α rβ) → UnificationSteps Γ Ξ Γ Ξ

  data UnificationStops : Context α → TelescopicEq α rβ → Set where
    StopCons :
      (Γ : Context α) (Γ' : Context α')
      → (Ξ : TelescopicEq α rβ) (Ξ' : TelescopicEq α' rβ')
      → UnificationSteps Γ Ξ Γ' Ξ' → UnificationStop Γ' Ξ'
      → UnificationStops Γ Ξ

  infix 3 _,_↣ᵤ⋆_,_
  infix 3 _,_↣ᵤ⋆⊥
  _,_↣ᵤ⋆_,_ = UnificationSteps
  _,_↣ᵤ⋆⊥ = UnificationStops
{- End of module UnificationStepAndStop -}
open UnificationStepAndStop public
