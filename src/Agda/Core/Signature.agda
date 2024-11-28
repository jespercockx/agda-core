open import Scope

open import Haskell.Prelude hiding (All; s; t)
open import Haskell.Extra.Dec using (ifDec)
open import Haskell.Extra.Erase
open import Haskell.Law.Equality
open import Haskell.Law.Semigroup.Def
open import Haskell.Law.Monoid.Def

open import Utils.Tactics using (auto)

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Utils
open import Agda.Core.Syntax

module Agda.Core.Signature {{@0 globals : Globals}} where

private open module @0 G = Globals globals

private variable
  @0 x : Name
  @0 α β γ : Scope Name

{- Telescopes are like contexts, mapping variables to types.
   Unlike contexts, they aren't closed.
   Telescope α β is like an extension of Context α with β.-}
data Telescope (@0 α : Scope Name) : @0 Scope Name → Set where
  EmptyTel  : Telescope α mempty
  ExtendTel : (@0 x : Name) → Type α → Telescope (x ◃ α) β  → Telescope α (x ◃ β)

pattern ⌈⌉ = EmptyTel
infix 6 ⌈_∶_◃_⌉
pattern ⌈_∶_◃_⌉ x t Δ = ExtendTel x t Δ

{-# COMPILE AGDA2HS Telescope #-}

opaque
  unfolding Scope

  caseTelEmpty : (tel : Telescope α mempty)
               → (@0 {{tel ≡ ⌈⌉}} → d)
               → d
  caseTelEmpty ⌈⌉ f = f

  caseTelBind : (tel : Telescope α (x ◃ β))
              → ((a : Type α) (rest : Telescope (x ◃ α) β) → @0 {{tel ≡ ExtendTel x a rest}} → d)
              → d
  caseTelBind ⌈ _ ∶ a ◃ tel ⌉ f = f a tel

{-# COMPILE AGDA2HS caseTelEmpty #-}
{-# COMPILE AGDA2HS caseTelBind #-}

record Constructor (@0 pars : Scope Name) (@0 ixs : Scope Name) (@0 c : NameIn conScope) : Set where
  field
    conTelescope : Telescope pars (fieldScope c)
    conIndices   : ixs ⇒ (revScope (fieldScope c) <> pars)
open Constructor public

{-# COMPILE AGDA2HS Constructor #-}

record Datatype (@0 pars : Scope Name) (@0 ixs : Scope Name) : Set where
  field
    dataConstructorScope : Scope Name
    dataSort             : Sort pars
    dataParameterTel     : Telescope mempty pars
    dataIndexTel         : Telescope pars ixs
    dataConstructors     : ((⟨ c ⟩ cp) : NameIn  dataConstructorScope)
                         → Σ (c ∈ conScope) (λ p → Constructor pars ixs (⟨ c ⟩ p))
open Datatype public

{-# COMPILE AGDA2HS Datatype #-}

data Definition : Set where
  FunctionDef : (funBody : Term mempty) → Definition

{-# COMPILE AGDA2HS Definition #-}

record Signature : Set where
  field
    sigData : (d : NameIn dataScope)
            → Datatype (dataParScope d) (dataIxScope d)
    sigDefs : (f : NameIn defScope)
            → Type (mempty {{iMonoidScope}}) × Definition
open Signature public

{-# COMPILE AGDA2HS Signature #-}

getType : Signature → (x : NameIn defScope) → Type mempty
getType sig x = fst defs
  where
    -- inlining this seems to trigger a bug in agda2hs
    -- TODO: investigate further
    defs = sigDefs sig x

{-# COMPILE AGDA2HS getType #-}

getDefinition : Signature → (x : NameIn defScope) → Definition
getDefinition sig x = snd defs
  where
    -- see above
    defs = sigDefs sig x

{-# COMPILE AGDA2HS getDefinition #-}

getBody : Signature → (x : NameIn defScope) → Term mempty
getBody sig x = case getDefinition sig x of λ where
  (FunctionDef body) → body

{-# COMPILE AGDA2HS getBody #-}

getConstructor : ((⟨ c ⟩ cp) : NameIn conScope)
               → ∀ {@0 pars ixs} (d : Datatype pars ixs)
               → Maybe (∃[ cd ∈ (c ∈ dataConstructorScope d) ]
                         fst (dataConstructors d (⟨ c ⟩ cd)) ≡ cp)
getConstructor c d =
  findAll (tabulateAll (rezz (dataConstructorScope d)) (λ _ → tt))
      λ _ p → ifEqualNamesIn (⟨ _ ⟩ fst (dataConstructors d (⟨ _ ⟩ p))) c
        (λ where {{refl}} → Just (p ⟨ refl ⟩))
        Nothing

{-# COMPILE AGDA2HS getConstructor #-}

weakenTel : α ⊆ γ → Telescope α β → Telescope γ β
weakenTel p ⌈⌉ = ⌈⌉
weakenTel p ⌈ x ∶ ty ◃ t ⌉ = ⌈ x ∶ (weaken p ty) ◃ (weakenTel (subBindKeep p) t) ⌉

{-# COMPILE AGDA2HS weakenTel #-}

instance
  iWeakenTel : Weaken (λ α → Telescope α β)
  iWeakenTel .weaken = weakenTel
{-# COMPILE AGDA2HS iWeakenTel #-}

rezzTel : Telescope α β → Rezz β
rezzTel ⌈⌉ = rezz _
rezzTel ⌈ x ∶ ty ◃ t ⌉ = rezzCong (λ t → singleton x <> t) (rezzTel t)

{-# COMPILE AGDA2HS rezzTel #-}


addTel : Telescope α β → Telescope ((~ β) <> α) γ → Telescope α (β <> γ)
addTel {α = α} {γ = γ} ⌈⌉ Δ₀ = do
  let Δ₁ : Telescope (mempty <> α) γ
      Δ₁ = subst0 (λ ∅ → Telescope (∅ <> α) γ) revsIdentity Δ₀
      Δ₂ : Telescope α γ
      Δ₂ = subst0 (λ α₀ → Telescope α₀ γ) (leftIdentity α) Δ₁
  subst0 (λ γ₀ → Telescope α γ₀) (sym (leftIdentity γ)) Δ₂
addTel {α = α} {γ = γ} ⌈ x ∶  ty ◃ s ⌉ Δ = do
  let Δ₁ : Telescope ((~ _ ▹ x) <> α) γ
      Δ₁ = subst0 (λ  β₀ → Telescope (β₀ <> α) γ) (revsBindComp _ x) Δ
      Δ₂ : Telescope (~ _ <> (x ◃ α)) γ
      Δ₂ = subst0 (λ α₀ → Telescope α₀ γ) (sym (associativity (~ _) [ x ] α)) Δ₁
      Ξ : Telescope (x ◃ α) (_ <> γ)
      Ξ = addTel s Δ₂
      Ξ' : Telescope α (x ◃ (_ <> γ))
      Ξ' = ⌈ x ∶ ty ◃ Ξ ⌉
      @0 e : x ◃ (_ <> γ) ≡ (x ◃ _) <> γ
      e = associativity [ x ] _ γ
  subst0 (λ γ₀ → Telescope α γ₀) e Ξ'

{-# COMPILE AGDA2HS addTel #-}

addTelrev : Telescope α (~ β) → Telescope (β <> α) γ → Telescope α ((~ β) <> γ)
addTelrev {α = α} {β = β} {γ = γ} Σ Δ = do
  let Δ₁ : Telescope (~ ~ β <> α) γ
      Δ₁ = subst0 (λ β₀ → Telescope (β₀ <> α) γ) (sym (revsInvolution β)) Δ
  addTel Σ Δ₁

{-# COMPILE AGDA2HS addTelrev #-}

{-
opaque
  unfolding revScope
  addTel : Telescope α β → Telescope ((~ β) <> α) γ → Telescope α (β <> γ)
  addTel ⌈⌉ Δ = Δ
  addTel {α = α} {β = _ ∷ β} {γ = γ} ⌈ x ∶  ty ◃ Σ ⌉ Δ = do
    let Δ₁ : Telescope ((~ β ▹ x) <> α) γ
        Δ₁ = subst0 (λ  β₀ → Telescope (β₀ <> α) γ) (revsBindComp β x) Δ
        Δ₂ : Telescope (~ β <> (x ◃ α)) γ
        Δ₂ = subst0 (λ α₀ → Telescope α₀ γ) (sym (associativity (~ β) [ x ] α)) Δ₁
    ⌈ x ∶ ty ◃ addTel Σ Δ₂ ⌉
-}