open import Scope

open import Haskell.Prelude hiding (All; s; t)
open import Haskell.Extra.Dec using (ifDec)
open import Haskell.Extra.Erase
open import Haskell.Law.Equality hiding (subst)
open import Haskell.Law.Semigroup.Def
open import Haskell.Law.Monoid.Def

open import Utils.Tactics using (auto)

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Utils
open import Agda.Core.Syntax
open import Agda.Core.Substitute


module Agda.Core.Signature {{@0 globals : Globals}} where

private open module @0 G = Globals globals

private variable
  @0 x : Name
  @0 α β γ : Scope Name
  @0 rβ rγ : RScope Name

opaque
  unfolding RScope

  caseTelEmpty : (tel : Telescope α mempty)
               → (@0 {{tel ≡ ⌈⌉}} → d)
               → d
  caseTelEmpty ⌈⌉ f = f

  caseTelBind : (tel : Telescope α (x ◂ rβ))
              → ((a : Type α) (rest : Telescope (α ▸ x) rβ) → @0 {{tel ≡ ExtendTel x a rest}} → d)
              → d
  caseTelBind  (_ ∶ a ◂ tel) f = f a tel

{-# COMPILE AGDA2HS caseTelEmpty #-}
{-# COMPILE AGDA2HS caseTelBind #-}

record Constructor (@0 pars : RScope Name) (@0 ixs : RScope Name) (@0 c : NameIn conScope) : Set where
  field
    conIndTel : Telescope (extScope mempty pars) (fieldScope c)                -- the TypeS of the indexes of c
    conIx     :  TermS (extScope (extScope mempty pars) (fieldScope c)) ixs    -- how the indexes are constructred given parameters and c indices

  evalConIndTel : {@0 α : Scope Name} → TermS α pars → Telescope α (fieldScope c)
  evalConIndTel tPars = subst (extSubst ⌈⌉ tPars) conIndTel

  evalConIx : {@0 α : Scope Name} → TermS α pars → TermS α (fieldScope c) → TermS α ixs
  evalConIx tPars tInd = subst (extSubst (extSubst ⌈⌉ tPars) tInd) conIx
open Constructor public

{-# COMPILE AGDA2HS Constructor #-}

record Datatype (@0 pars : RScope Name) (@0 ixs : RScope Name) : Set where
  field
    dataConstructorScope : Scope Name
    dataSort             : Sort (extScope mempty pars)
    dataParTel           : Telescope mempty pars
    dataIxTel            : Telescope (extScope mempty pars) ixs
    dataConstructors     : ((⟨ c ⟩ cp) : NameIn  dataConstructorScope)
                         → Σ (c ∈ conScope) (λ p → Constructor pars ixs (⟨ c ⟩ p))

  evalDataSort : {@0 α : Scope Name} → TermS α pars → Sort α
  evalDataSort tPars = subst (extSubst ⌈⌉ tPars) dataSort

  evalDataParTel : {@0 α : Scope Name} → Telescope α pars
  evalDataParTel = subst ⌈⌉ dataParTel

  evalDataIxTel : {@0 α : Scope Name} → TermS α pars → Telescope α ixs
  evalDataIxTel tPars = subst (extSubst ⌈⌉ tPars) dataIxTel
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

getType : Signature → (x : NameIn defScope) → Type α
getType sig x = subst ⌈⌉ (fst defs)
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

weakenTel : α ⊆ γ → Telescope α rβ → Telescope γ rβ
weakenTel p ⌈⌉ = ⌈⌉
weakenTel p (x ∶ ty ◂ t) = x ∶ (weaken p ty) ◂ (weakenTel (subBindKeep p) t)

{-# COMPILE AGDA2HS weakenTel #-}

instance
  iWeakenTel : Weaken (λ α → Telescope α rβ)
  iWeakenTel .weaken = weakenTel
{-# COMPILE AGDA2HS iWeakenTel #-}

rezzTel : Telescope α rβ → Rezz rβ
rezzTel ⌈⌉ = rezz _
rezzTel (x ∶ ty ◂ t) = rezzCong (λ t → x ◂ t) (rezzTel t)

{-# COMPILE AGDA2HS rezzTel #-}

opaque
  addTel : Telescope α rβ → Telescope (extScope α rβ) rγ → Telescope α (rβ <> rγ)
  addTel ⌈⌉ tel0 =
    subst0 (λ α → Telescope α _) extScopeEmpty
    (subst0 (Telescope _) (sym (leftIdentity _)) tel0)
  addTel {α = α} {rγ = rγ} (x ∶  ty ◂ s) tel0 =
    subst0 (Telescope α) (associativity (x ◂) _ rγ)
    (x ∶ ty ◂ addTel s (subst0 (λ δ → Telescope δ rγ) extScopeBind tel0))
  {-# COMPILE AGDA2HS addTel #-}
