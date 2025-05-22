open import Scope

open import Haskell.Prelude hiding (All; c; d; s; t)
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
  @0 x      : Name
  @0 α β γ  : Scope Name
  @0 rβ rγ  : RScope Name
  @0 d      : NameData
opaque
  unfolding RScope

  caseTelEmpty : (tel : Telescope α mempty)
               → (@0 {{tel ≡ ⌈⌉}} → e)
               → e
  caseTelEmpty ⌈⌉ f = f

  caseTelBind : (tel : Telescope α (x ◂ rβ))
              → ((a : Type α) (rest : Telescope (α ▸ x) rβ) → @0 {{tel ≡ ExtendTel x a rest}} → e)
              → e
  caseTelBind  (_ ∶ a ◂ tel) f = f a tel

{-# COMPILE AGDA2HS caseTelEmpty #-}
{-# COMPILE AGDA2HS caseTelBind #-}

record Constructor {@0 d : NameData} (@0 c : NameCon d) : Set where
  private
    @0 pars : RScope Name
    pars = dataParScope d
    @0 ixs : RScope Name
    ixs  = dataIxScope d
  field
    conIndTel : Telescope (extScope mempty pars) (fieldScope c)                -- the TypeS of the indexes of c
    conIx     :  TermS (extScope (extScope mempty pars) (fieldScope c)) ixs    -- how the indexes are constructred given parameters and c indices
open Constructor public
{-# COMPILE AGDA2HS Constructor #-}

evalConIndTel : {@0 c : NameCon d} → (con : Constructor c) →  TermS α (dataParScope d) → Telescope α (fieldScope c)
evalConIndTel con tPars = subst (extSubst ⌈⌉ tPars) (conIndTel con)
{-# COMPILE AGDA2HS evalConIndTel #-}

evalConIx : {@0 c : NameCon d} → (con : Constructor c) → TermS α (dataParScope d) → TermS α (fieldScope c) → TermS α (dataIxScope d)
evalConIx con tPars tInd = subst (extSubst (extSubst ⌈⌉ tPars) tInd) (conIx con)
{-# COMPILE AGDA2HS evalConIx #-}


record Datatype (@0 d : NameData) : Set where
  private
    @0 pars : RScope Name
    pars = dataParScope d
    @0 ixs : RScope Name
    ixs  = dataIxScope d
  field
    dataSort             : Sort (extScope mempty pars)
    dataParTel           : Telescope mempty pars
    dataIxTel            : Telescope (extScope mempty pars) ixs
    dataConstructors     : List (NameCon d) -- for Haskell side
open Datatype public
{-# COMPILE AGDA2HS Datatype #-}

evalDataSort : (dt : Datatype d) → TermS α (dataParScope d) → Sort α
evalDataSort dt tPars = subst (extSubst ⌈⌉ tPars) (dataSort dt)
{-# COMPILE AGDA2HS evalDataSort #-}

evalDataParTel : (dt : Datatype d) → Telescope α (dataParScope d)
evalDataParTel dt = subst ⌈⌉ (dataParTel dt)
{-# COMPILE AGDA2HS evalDataParTel #-}

evalDataIxTel : (dt : Datatype d) → TermS α (dataParScope d) → Telescope α (dataIxScope d)
evalDataIxTel dt tPars = subst (extSubst ⌈⌉ tPars) (dataIxTel dt)
{-# COMPILE AGDA2HS evalDataIxTel #-}


data SigDefinition : Set where
  FunctionDef : (funBody : Term mempty) → SigDefinition
{-# COMPILE AGDA2HS SigDefinition #-}

record Signature : Set where
  field
    sigData : (d : NameData) → Datatype d
    sigDefs : (f : NameIn defScope)  → Type mempty × SigDefinition
    sigCons : (d : NameData) (c : NameCon d) → Constructor c -- Do not erase d, (d,c) is needed to find the constructor
open Signature public

{-# COMPILE AGDA2HS Signature #-}

getType : Signature → (x : NameIn defScope) → Type α
getType sig x = subst ⌈⌉ (fst defs)
  where
    -- inlining this seems to trigger a bug in agda2hs
    -- TODO: investigate further
    defs = sigDefs sig x

{-# COMPILE AGDA2HS getType #-}

getDefinition : Signature → (x : NameIn defScope) → SigDefinition
getDefinition sig x = snd defs
  where
    -- see above
    defs = sigDefs sig x

{-# COMPILE AGDA2HS getDefinition #-}

getBody : Signature → (x : NameIn defScope) → Term mempty
getBody sig x = case getDefinition sig x of λ where
  (FunctionDef body) → body

{-# COMPILE AGDA2HS getBody #-}

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



{- Definitions for haskell backend -}
data Defn : Set where
  FunctionDefn : (funBody : Term mempty) → Defn
  DatatypeDefn :  (@0 d : NameData) → Datatype d → Defn
  ConstructorDefn : (@0 d : NameData) (@0 c : NameCon d) → Constructor c → Defn
{-# COMPILE AGDA2HS Defn #-}


record Definition : Set where
  field
    defName : String
    defType : Type mempty
    theDef : Defn
open Definition public
{-# COMPILE AGDA2HS Definition #-}
