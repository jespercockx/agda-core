open import Haskell.Prelude           hiding (All; coerce; a; b; c; d)
open import Haskell.Law.Equality      using (sym; subst0)
open import Haskell.Law.Monoid.Def    using (leftIdentity; rightIdentity)
open import Haskell.Law.Semigroup.Def using (associativity)
open import Haskell.Extra.Erase

import Agda.Core.GlobalScope
open import Agda.Core.Name
open import Agda.Core.Utils

module Agda.Core.Syntax.Term
  {{@0 globals : Agda.Core.GlobalScope.Globals}}
  where

open Agda.Core.GlobalScope using (Globals) public
private open module @0 G = Globals globals

data Term     (@0 α : Scope Name) : Set
data TermS    (@0 α : Scope Name) : (@0 rβ : RScope Name) → Set
record Type   (@0 α : Scope Name) : Set
data Sort     (@0 α : Scope Name) : Set
data Branch   (@0 α : Scope Name) {@0 d : NameData} (@0 c : NameCon d) : Set
data Branches (@0 α : Scope Name) (@0 d : NameData) : @0 RScope (NameCon d) → Set


data Term α where
  TVar  : (x : NameIn α) → Term α
  TDef  : (d : NameIn defScope) → Term α
  TData : (d : NameData)
        → (TermS α (dataParScope d))
        → (TermS α (dataIxScope d))
        → Term α
  TCon  : {d : NameData} (c : NameCon d)
        → (TermS α (fieldScope c)) → Term α
  TLam  : (@0 x : Name) (v : Term (α ▸ x)) → Term α
  TApp  : (u : Term α) (v : Term α) → Term α
  TProj : (u : Term α) (x : NameIn defScope) → Term α
  TCase : {@0 x : Name}
        → (d : NameData)                                  -- Datatype of the variable we are splitting on
        → Rezz (dataIxScope d)                            -- Run-time representation of index scope
        → (u : Term α)                                    -- Term we are casing on
        → (bs : Branches α d (AllNameCon d))              -- Branches (one for each constructor of d)
        → (m : Type ((extScope α (dataIxScope d)) ▸ x))   -- Return type
        → Term α
  TPi   : (@0 x : Name) (u : Type α) (v : Type (α ▸ x)) → Term α
  TSort : Sort α → Term α
  TLet  : (@0 x : Name) (u : Term α) (v : Term (α ▸ x)) → Term α
  TAnn  : (u : Term α) (t : Type α) → Term α
  -- TODO: literals

data TermS α where
  TSNil  : TermS α mempty
  TSCons : {@0 rβ : RScope Name} {@0 x : Name}
    → Term α → TermS α rβ → TermS α (x ◂ rβ)

pattern ⌈⌉ = TSNil
pattern _↦_◂_ x t s = TSCons {x = x} t s

record Type α where
  inductive
  constructor El
  field
    typeSort : Sort α
    unType   : Term α
open Type public

data Sort α where
  STyp : Nat → Sort α
  -- TODO: universe polymorphism

data Branch α c where
  BBranch : Rezz c → Rezz (fieldScope c)
          → Term (extScope α (fieldScope c)) → Branch α c

data Branches α d where
  BsNil  : Branches α d mempty
  BsCons : {@0 c : NameCon d} {@0 cs : RScope (NameCon d)}
    → Branch α c → Branches α d cs → Branches α d (c ◂ cs)

{-# COMPILE AGDA2HS Term deriving Show #-}
{-# COMPILE AGDA2HS TermS deriving Show #-}
{-# COMPILE AGDA2HS Type deriving Show #-}
{-# COMPILE AGDA2HS Sort deriving Show #-}
{-# COMPILE AGDA2HS Branch deriving Show #-}
{-# COMPILE AGDA2HS Branches deriving Show #-}


---------------------------------------------------------------------------------------------------
                                      {- Useful functions -}
---------------------------------------------------------------------------------------------------
private variable
  @0 x      : Name
  @0 α      : Scope Name
  @0 rβ rγ  : RScope Name
  @0 d      : NameData
  @0 c      : NameCon d
  @0 cs     : RScope (NameCon d)

-- shortcut fort sort and datatype

piSort : Sort α → Sort (α ▸ x) → Sort α
piSort (STyp a) (STyp b) = STyp (max a b)
{-# COMPILE AGDA2HS piSort #-}

funSort : Sort α → Sort α → Sort α
funSort (STyp a) (STyp b) = STyp (max a b)
{-# COMPILE AGDA2HS funSort #-}

sucSort : Sort α → Sort α
sucSort (STyp a) = STyp (1 + a)
{-# COMPILE AGDA2HS sucSort #-}

sortType : Sort α → Type α
sortType s = El (sucSort s) (TSort s)
{-# COMPILE AGDA2HS sortType #-}

dataType : (d : NameData)
         → Sort α
         → (pars : TermS α (dataParScope d))
         → (ixs : TermS α (dataIxScope d))
         → Type α
dataType d ds pars ixs = El ds (TData d pars ixs)
{-# COMPILE AGDA2HS dataType #-}

-- case on Terms

opaque
  unfolding RScope
  caseBsNil : (bs : Branches α d mempty)
            → (@0 ⦃ bs ≡ BsNil ⦄ → e)
            → e
  caseBsNil BsNil f = f
  {-# COMPILE AGDA2HS caseBsNil #-}

  caseBsCons : (bs : Branches α d (c ◂ cs))
             → ((bh : Branch α c) (bt : Branches α d cs) → @0 ⦃ bs ≡ BsCons bh bt ⦄ → e)
             → e
  caseBsCons (BsCons bh bt) f = f bh bt
  {-# COMPILE AGDA2HS caseBsCons #-}

opaque
  unfolding RScope
  caseTermSNil : (ts : TermS α mempty)
               → (@0 ⦃ ts ≡ ⌈⌉ ⦄ → e)
               → e
  caseTermSNil ⌈⌉ f = f
  {-# COMPILE AGDA2HS caseTermSNil #-}

  caseTermSCons : (ts : TermS α (x ◂ rβ))
            → ((t : Term α) (ts0 : TermS α rβ) → @0 ⦃ ts ≡ x ↦ t ◂ ts0 ⦄ → e)
            → e
  caseTermSCons (x ↦ t ◂ ts0) f = f t ts0
  {-# COMPILE AGDA2HS caseTermSCons #-}

-- Resurection of Scope/RScope

rezzBranches : Branches α d cs → Rezz cs
rezzBranches BsNil = rezz mempty
rezzBranches (BsCons {c = c} bh bt) = rezzCong (λ cs → c ◂ cs) (rezzBranches bt)
{-# COMPILE AGDA2HS rezzBranches #-}

rezzTermS : TermS α rβ → Rezz rβ
rezzTermS ⌈⌉ = rezz _
rezzTermS (x ↦ u ◂ t) = rezzCong (λ t → x ◂ t) (rezzTermS t)
{-# COMPILE AGDA2HS rezzTermS #-}

-- others

applys : Term α → List (Term α) → Term α
applys v [] = v
applys v (u ∷ us) = applys (TApp v u) us
{-# COMPILE AGDA2HS applys #-}

unApps : Term α → Term α × List (Term α)
unApps (TApp u es2) =
  case unApps u of λ where
    (u' , es1) → (u' , (es1 ++ es2 ∷ []))
unApps u = (u , [])
{-# COMPILE AGDA2HS unApps #-}

applysComp : (t : Term α) → (el1 el2 : List (Term α)) → applys t (el1 ++ el2) ≡ applys (applys t el1) el2
applysComp t [] el2 = refl
applysComp t (x ∷ el1) el2 = applysComp (TApp t x) el1 el2

unAppsView : (t : Term α) → (uncurry applys) (unApps t) ≡ t
unAppsView (TApp t es)
  rewrite applysComp (fst (unApps t)) (snd (unApps t)) (es ∷ [])
  rewrite unAppsView t
  = refl
unAppsView (TVar _)          = refl
unAppsView (TDef _)          = refl
unAppsView (TData _ _ _)     = refl
unAppsView (TCon _ _)        = refl
unAppsView (TProj _ _)       = refl
unAppsView (TCase _ _ _ _ _) = refl
unAppsView (TLam _ _)        = refl
unAppsView (TPi _ _ _)       = refl
unAppsView (TSort _)         = refl
unAppsView (TLet _ _ _)      = refl
unAppsView (TAnn _ _)        = refl

concatTermS : TermS α rβ → TermS α rγ → TermS α (rβ <> rγ)
concatTermS {α = α} {rγ = rγ} ⌈⌉ t =
  subst0 (TermS α) (sym (leftIdentity rγ)) t
concatTermS {α = α} {rγ = rγ} (x ↦ u ◂ t1) t =
  subst0 (TermS α) (associativity (x ◂) _ rγ) (x ↦ u ◂ concatTermS t1 t)

opaque
  unfolding extScope
  termSrepeat : Rezz rβ → TermS (extScope α rβ) rβ
  termSrepeat (rezz []) = ⌈⌉
  termSrepeat (rezz (Erased x ∷ rβ)) = x ↦ TVar (⟨ x ⟩ inScopeInExtScope (rezz rβ) inHere) ◂ termSrepeat (rezz rβ)
  {-# COMPILE AGDA2HS termSrepeat #-}
