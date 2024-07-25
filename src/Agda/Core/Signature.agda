open import Scope

open import Haskell.Prelude hiding (All; s; t)
open import Haskell.Extra.Dec using (ifDec)
open import Haskell.Extra.Erase
open import Haskell.Law.Equality
open import Haskell.Law.Monoid
open import Utils.Tactics using (auto)

open import Agda.Core.GlobalScope using (Globals; Name)
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

{-# COMPILE AGDA2HS Telescope #-}

opaque
  unfolding Scope

  caseTelEmpty : (tel : Telescope α mempty)
               → (@0 {{tel ≡ EmptyTel}} → d)
               → d
  caseTelEmpty EmptyTel f = f

  caseTelBind : (tel : Telescope α (x ◃ β))
              → ((a : Type α) (rest : Telescope (x ◃ α) β) → @0 {{tel ≡ ExtendTel x a rest}} → d)
              → d
  caseTelBind (ExtendTel _ a tel) f = f a tel


{-# COMPILE AGDA2HS caseTelBind #-}

record Constructor (@0 pars : Scope Name) (@0 ixs : Scope Name) (@0 c : Name) (@0 cp  : c ∈ conScope) : Set where
  field
    conTelescope : Telescope pars (fieldScope c)
    conIndices   : ixs ⇒ (revScope (fieldScope c) <> pars)
open Constructor public

{-# COMPILE AGDA2HS Constructor #-}

record Datatype (@0 pars : Scope Name) (@0 ixs : Scope Name) : Set where
  field
    @0 dataConstructorScope : Scope Name
    dataSort                : Sort pars
    dataParameterTel        : Telescope mempty pars
    dataIndexTel            : Telescope pars ixs
    dataConstructors        : All (λ c → Σ (c ∈ conScope) (Constructor pars ixs c)) dataConstructorScope
open Datatype public

{-# COMPILE AGDA2HS Datatype #-}

data Definition : Set where
  FunctionDef : (funBody : Term mempty) → Definition

{-# COMPILE AGDA2HS Definition #-}

record Signature : Set where
  field
    sigData : (@0 d : Name) → {@(tactic auto) dp : d ∈ dataScope}
            → Datatype (dataParScope d) (dataIxScope d)
    sigDefs : (@0 f : Name) → {@(tactic auto) fp : f ∈ defScope}
            → Type (mempty {{iMonoidScope}}) × Definition
open Signature public

{-# COMPILE AGDA2HS Signature #-}

getType : Signature → (@0 x : Name) → {@(tactic auto) _ : x ∈ defScope} → Type mempty
getType sig x = fst defs
  where
    -- inlining this seems to trigger a bug in agda2hs
    -- TODO: investigate further
    defs = sigDefs sig x

{-# COMPILE AGDA2HS getType #-}

getDefinition : Signature → (@0 x : Name) → {@(tactic auto) _ : x ∈ defScope} → Definition
getDefinition sig x = snd defs
  where
    -- see above
    defs = sigDefs sig x

{-# COMPILE AGDA2HS getDefinition #-}

getBody : Signature → (@0 x : Name) → {@(tactic auto) _ : x ∈ defScope} → Term mempty
getBody sig x = case getDefinition sig x of λ where
  (FunctionDef body) → body

{-# COMPILE AGDA2HS getBody #-}

getConstructor : (@0 c : Name) {@(tactic auto) cp : c ∈ conScope}
               → ∀ {@0 pars ixs} (d : Datatype pars ixs)
               → Maybe (∃[ cd ∈ (c ∈ dataConstructorScope d) ]
                         fst (lookupAll (dataConstructors d) cd) ≡ cp)
getConstructor c {cp} d = findAll (allLookup (dataConstructors d)) dec
  where
    -- can't have a lambda take two arguments for agda2hs, so here's a local def
    dec : {@0 el : Name}
        → ∃ (el ∈ (dataConstructorScope d) × _)
            (λ where (i , pi) → lookupAll (dataConstructors d) i ≡ pi)
        → _
        → Maybe (∃[ cd ∈ (c ∈ dataConstructorScope d) ]
                  fst (lookupAll (dataConstructors d) cd) ≡ cp)
    dec ((i , (ci , con)) ⟨ ep ⟩) _ =
      ifDec (decIn cp ci)
            (λ where
              {{refl}} → Just (i ⟨ subst0 (λ (cci , ccon) → fst (lookupAll (dataConstructors d) i) ≡ cci) ep refl ⟩))
            Nothing

{-# COMPILE AGDA2HS getConstructor #-}

weakenTel : α ⊆ γ → Telescope α β → Telescope γ β
weakenTel p EmptyTel = EmptyTel
weakenTel p (ExtendTel x ty t) = ExtendTel x (weakenType p ty) (weakenTel (subBindKeep p) t)

{-# COMPILE AGDA2HS weakenTel #-}

rezzTel : Telescope α β → Rezz β
rezzTel EmptyTel = rezz _
rezzTel (ExtendTel x ty t) = rezzCong (λ t → singleton x <> t) (rezzTel t)

{-# COMPILE AGDA2HS rezzTel #-}

{-
addTel : Telescope α β → Telescope ((revScope β) <> α) γ → Telescope α (β <> γ)
addTel EmptyTel t =
  subst0 (Telescope _)
         (sym (leftIdentity _))
         (subst0 (λ s → Telescope s _)
                 (trans (cong (λ t → t <> _)
                         revScopeMempty)
                 (leftIdentity _))
                 t)
addTel (ExtendTel x ty s) t = {!!} -}
