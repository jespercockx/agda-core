open import Scope

open import Haskell.Prelude hiding (All; s; t)
open import Haskell.Extra.Dec using (ifDec)
open import Haskell.Extra.Erase
open import Haskell.Law.Equality
open import Haskell.Law.Monoid

open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Utils renaming (_,_ to _Σ,_)

module Agda.Core.Signature {@0 name  : Set} (@0 globals : Globals name) where

open import Agda.Core.Syntax globals
private open module @0 G = Globals globals

private variable
  @0 x : name
  @0 α β γ : Scope name

{- Telescopes are like contexts, mapping variables to types.
   Unlike contexts, they aren't closed.
   Telescope α β is like an extension of Context α with β.-}
data Telescope (@0 α : Scope name) : @0 Scope name → Set where
  EmptyTel  : Telescope α mempty
  ExtendTel : (@0 x : name) → Type α → Telescope (x ◃ α) β  → Telescope α (x ◃ β)

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

record Constructor (@0 pars : Scope name) (@0 c : name) (@0 cp  : c ∈ conScope) : Set
record Constructor pars c cp where
  field conTelescope : Telescope pars (fieldsOf cp)
open Constructor public

{-# COMPILE AGDA2HS Constructor #-}

record Datatype : Set where
  field @0 dataPars       :  Scope name
        @0 dataCons       :  Scope name
        dataSort          :  Sort dataPars
        dataParTel        :  Telescope ∅ dataPars
        dataConstructors  :  All  (λ c → Σ  (c ∈ conScope)
                                            (Constructor dataPars c))
                                  dataCons
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

getType : Signature → (@0 x : name) → x ∈ defScope → Type mempty
getType sig x p = fst (lookupAll sig p)

{-# COMPILE AGDA2HS getType #-}

getDefinition : Signature → (@0 x : name) → x ∈ defScope → Definition
getDefinition sig x p = snd (lookupAll sig p)

{-# COMPILE AGDA2HS getDefinition #-}

getBody : Signature → (@0 x : name) → x ∈ defScope → Maybe (Term mempty)
getBody sig x p = case getDefinition sig x p of λ where
  (FunctionDef body) → Just body
  (DatatypeDef _)    → Nothing
  RecordDef          → Nothing

{-# COMPILE AGDA2HS getBody #-}

getConstructor : (@0 c : name) (cp : c ∈ conScope) (d : Datatype)
               → Maybe (∃[ cd ∈ (c ∈ dataCons d) ]
                         fst (lookupAll (dataConstructors d) cd) ≡ cp)
getConstructor c cp d = findAll (allLookup (dataConstructors d)) dec
  where
    -- can't have a lambda take two arguments for agda2hs, so here's a local def
    dec : {@0 el : name}
        → ∃ ((el ∈ (dataCons d)) × _)
           (λ where (i , pi) → lookupAll (dataConstructors d) i ≡ pi)
        → _
        → Maybe (∃[ cd ∈ (c ∈ dataCons d) ]
                  fst (lookupAll (dataConstructors d) cd) ≡ cp)
    dec ((i , (ci Σ, con)) ⟨ ep ⟩) _ =
      ifDec (decIn cp ci)
            (λ where
              {{refl}} → Just (i ⟨ subst0 (λ (cci Σ, ccon) → fst (lookupAll (dataConstructors d) i) ≡ cci) ep refl ⟩))
            Nothing

{-# COMPILE AGDA2HS getConstructor #-}

weakenTel : α ⊆ γ → Telescope α β → Telescope γ β
weakenTel p EmptyTel = EmptyTel
weakenTel p (ExtendTel x ty t) = ExtendTel x (weakenType p ty) (weakenTel (subBindKeep p) t)

{-# COMPILE AGDA2HS weakenTel #-}

rezzTel : Telescope α β → Rezz _ β
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


opaque
  unfolding caseTelEmpty caseTelBind

  SignatureThings : Set₁
  SignatureThings = Set
