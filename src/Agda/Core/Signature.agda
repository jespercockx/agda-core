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
    conTelescope : Telescope pars (lookupAll fieldScope cp)
    conIndices   : ixs ⇒ (revScope (lookupAll fieldScope cp) <> pars)
open Constructor public

{-# COMPILE AGDA2HS Constructor #-}

record Datatype : Set where
  field
    @0 dataParameterScope   : Scope Name
    @0 dataIndexScope       : Scope Name
    @0 dataConstructorScope : Scope Name
    dataSort                : Sort dataParameterScope
    dataParameterTel        : Telescope mempty dataParameterScope
    dataIndexTel            : Telescope dataParameterScope dataIndexScope
    dataConstructors        : All (λ c → Σ (c ∈ conScope) (Constructor dataParameterScope dataIndexScope c)) dataConstructorScope
open Datatype public

{-# COMPILE AGDA2HS Datatype #-}

data Definition : Set where
  FunctionDef : (funBody : Term mempty) → Definition
  DatatypeDef : (datatypeDef : Datatype) → Definition
  RecordDef   : {- TODO → -} Definition

{-# COMPILE AGDA2HS Definition #-}

Signature : Set
Signature = All (λ _ → Type (mempty {{iMonoidScope}}) × Definition) defScope

{-# COMPILE AGDA2HS Signature #-}

getType : Signature → (@0 x : Name) → {@(tactic auto) _ : x ∈ defScope} → Type mempty
getType sig x {p} = fst (lookupAll sig p)

{-# COMPILE AGDA2HS getType #-}

getDefinition : Signature → (@0 x : Name) → {@(tactic auto) _ : x ∈ defScope} → Definition
getDefinition sig x {p} = snd (lookupAll sig p)

{-# COMPILE AGDA2HS getDefinition #-}

getBody : Signature → (@0 x : Name) → {@(tactic auto) _ : x ∈ defScope} → Maybe (Term mempty)
getBody sig x = case getDefinition sig x of λ where
  (FunctionDef body) → Just body
  (DatatypeDef _)    → Nothing
  RecordDef          → Nothing

{-# COMPILE AGDA2HS getBody #-}

getConstructor : (@0 c : Name) {@(tactic auto) cp : c ∈ conScope} (d : Datatype)
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
