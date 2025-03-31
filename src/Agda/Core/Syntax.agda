open import Scope

open import Haskell.Prelude hiding (All; coerce; a; b; c)
open import Haskell.Law.Equality using (sym; subst0)
open import Haskell.Law.Monoid.Def using (leftIdentity; rightIdentity)
open import Haskell.Law.Semigroup.Def using (associativity)
open import Haskell.Prim.Tuple using (first)
open import Haskell.Extra.Erase

-- NOTE(flupe): comes from scope library, should be moved upstream probably
open import Utils.Misc
open import Utils.Tactics using (auto)

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Utils

module Agda.Core.Syntax
  {{@0 globals : Globals}}
  where

private open module @0 G = Globals globals

private variable
  @0 x a b c : Name
  @0 α β γ cs : Scope Name
  @0 rβ rγ : RScope Name

data Term   (@0 α : Scope Name) : Set
data Sort   (@0 α : Scope Name) : Set
record Type (@0 α : Scope Name) : Set
data Branch (@0 α : Scope Name) : @0 Name → Set
data Branches (@0 α : Scope Name) : @0 Scope Name → Set

record Type α where
  inductive
  constructor El
  field
    typeSort : Sort α
    unType   : Term α
open Type public
{-# COMPILE AGDA2HS Type deriving Show #-}

data TermS : (@0 α : Scope Name) (@0 rβ : RScope Name) → Set where
  TSNil  : TermS α mempty
  TSCons :  Term α → TermS α rβ → TermS α (x ◂ rβ)
{-# COMPILE AGDA2HS TermS deriving Show #-}

pattern ⌈⌉ = TSNil
pattern _↦_◂_ x t s = TSCons {x = x} t s

{- Telescopes are like contexts, mapping variables to types.
   Unlike contexts, they aren't closed.
   Telescope α β is like an extension of Context α with β.-}
data Telescope (@0 α : Scope Name) : @0 RScope Name → Set where
  EmptyTel  : Telescope α mempty
  ExtendTel : (@0 x : Name) → Type α → Telescope (α ▸ x) rβ  → Telescope α (x ◂ rβ)

pattern ⌈⌉ = EmptyTel
infix 6 _∶_◂_
pattern _∶_◂_ x t Δ = ExtendTel x t Δ

{-# COMPILE AGDA2HS Telescope #-}
-- This should ideally be the following:
--   TermS α β = All (λ _ → Term β) α
-- but All being opaque prevents the positivity checker to do its job
-- see #6970

data Term α where
  TVar  : (x : NameIn α) → Term α
  TDef  : (d : NameIn defScope) → Term α
  TData : (d : NameIn dataScope)
        → (TermS α (dataParScope d))
        → (TermS α (dataIxScope d))
        → Term α
  TCon  : (c : NameIn conScope)
        → (TermS α (fieldScope c)) → Term α
  TLam  : (@0 x : Name) (v : Term (α ▸ x)) → Term α
  TApp  : (u : Term α) (v : Term α) → Term α
  TProj : (u : Term α) (x : NameIn defScope) → Term α
  TCase : (d : NameIn dataScope)                   -- Datatype of the variable we are splitting on
        → Rezz (dataIxScope d)                     -- Run-time representation of index scope
        → (u : Term α)                             -- Term we are casing on
        → (bs : Branches α cs)                     -- Branches (one for each constructor of d)
        → (m : Type ((extScope α (dataIxScope d)) ▸ x))  -- Return type
        → Term α
  TPi   : (@0 x : Name) (u : Type α) (v : Type (α ▸ x)) → Term α
  TSort : Sort α → Term α
  TLet  : (@0 x : Name) (u : Term α) (v : Term (α ▸ x)) → Term α
  TAnn  : (u : Term α) (t : Type α) → Term α
  -- TODO: literals
{-# COMPILE AGDA2HS Term deriving Show #-}

data Sort α where
  STyp : Nat → Sort α
  -- TODO: universe polymorphism
{-# COMPILE AGDA2HS Sort deriving Show #-}

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

data Branch α where
  BBranch : (c : NameIn conScope)
          → Rezz (fieldScope c)
          → Term (extScope α (fieldScope c)) → Branch α (proj₁ c)
{-# COMPILE AGDA2HS Branch deriving Show #-}

data Branches α where
  BsNil : Branches α mempty
  BsCons : Branch α c → Branches α cs → Branches α (cs ▸ c)
{-# COMPILE AGDA2HS Branches deriving Show #-}

opaque
  unfolding Scope

  caseBsNil : (bs : Branches α mempty)
            → (@0 ⦃ bs ≡ BsNil ⦄ → d)
            → d
  caseBsNil BsNil f = f
  {-# COMPILE AGDA2HS caseBsNil #-}

  caseBsCons : (bs : Branches α (cs ▸ c))
             → ((bh : Branch α c) (bt : Branches α cs) → @0 ⦃ bs ≡ BsCons bh bt ⦄ → d)
             → d
  caseBsCons (BsCons bh bt) f = f bh bt
  {-# COMPILE AGDA2HS caseBsCons #-}

opaque
  unfolding RScope
  caseTermSNil : (ts : TermS α mempty)
               → (@0 ⦃ ts ≡ ⌈⌉ ⦄ → d)
               → d
  caseTermSNil ⌈⌉ f = f
  {-# COMPILE AGDA2HS caseTermSNil #-}

  caseTermSCons : (ts : TermS α (x ◂ rβ))
            → ((t : Term α) (ts0 : TermS α rβ) → @0 ⦃ ts ≡ x ↦ t ◂ ts0 ⦄ → d)
            → d
  caseTermSCons (x ↦ t ◂ ts0) f = f t ts0
  {-# COMPILE AGDA2HS caseTermSCons #-}

rezzBranches : Branches α β → Rezz β
rezzBranches BsNil = rezz mempty
rezzBranches (BsCons {c = c} bh bt) = rezzCong (λ cs → cs ▸ c) (rezzBranches bt)
{-# COMPILE AGDA2HS rezzBranches #-}

rezzTermS : TermS α rβ → Rezz rβ
rezzTermS ⌈⌉ = rezz _
rezzTermS (x ↦ u ◂ t) = rezzCong (λ t → x ◂ t) (rezzTermS t)
{-# COMPILE AGDA2HS rezzTermS #-}

allBranches : Branches α β → All (λ c → c ∈ conScope) β
allBranches BsNil = allEmpty
allBranches (BsCons (BBranch (⟨ _ ⟩ ci) _ _) bs) = allJoin (allBranches bs) (allSingl ci)
{-# COMPILE AGDA2HS allBranches #-}

applys : Term γ → List (Term γ) → Term γ
applys {γ = γ} v [] = v
applys {γ = γ} v (u ∷ us) = applys (TApp v u) us
{-# COMPILE AGDA2HS applys #-}

dataType : (d : NameIn dataScope)
         → Sort α
         → (pars : TermS α (dataParScope d))
         → (ixs : TermS α (dataIxScope d))
         → Type α
dataType d ds pars ixs = El ds (TData d pars ixs)
{-# COMPILE AGDA2HS dataType #-}

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
unAppsView (TVar _) = refl
unAppsView (TDef _) = refl
unAppsView (TData _ _ _) = refl
unAppsView (TCon _ _) = refl
unAppsView (TProj _ _) = refl
unAppsView (TCase _ _ _ _ _) = refl
unAppsView (TLam _ _) = refl
unAppsView (TPi _ _ _) = refl
unAppsView (TSort _) = refl
unAppsView (TLet _ _ _) = refl
unAppsView (TAnn _ _) = refl

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


weakenTerm     : α ⊆ β → Term α → Term β
weakenSort     : α ⊆ β → Sort α → Sort β
weakenType     : α ⊆ β → Type α → Type β
weakenBranch   : α ⊆ β → Branch α c → Branch β c
weakenBranches : α ⊆ β → Branches α cs → Branches β cs
weakenTermS    : α ⊆ β → TermS α rγ → TermS β rγ

weakenTerm p (TVar (⟨ x ⟩ k))  = TVar (⟨ x ⟩ coerce p k)
weakenTerm p (TDef d)          = TDef d
weakenTerm p (TData d ps is)   = TData d (weakenTermS p ps) (weakenTermS p is)
weakenTerm p (TCon c vs)       = TCon c (weakenTermS p vs)
weakenTerm p (TLam x v)        = TLam x (weakenTerm (subBindKeep p) v)
weakenTerm p (TApp u e)        = TApp (weakenTerm p u) (weakenTerm p e)
weakenTerm p (TProj u x)       = TProj (weakenTerm p u) x
weakenTerm p (TCase d r u bs m) = TCase d r (weakenTerm p u) (weakenBranches p bs) (weakenType (subBindKeep (subExtScopeKeep r p)) m)
weakenTerm p (TPi x a b)       = TPi x (weakenType p a) (weakenType (subBindKeep p) b)
weakenTerm p (TSort α)         = TSort (weakenSort p α)
weakenTerm p (TLet x v t)      = TLet x (weakenTerm p v) (weakenTerm (subBindKeep p) t)
weakenTerm p (TAnn u t)        = TAnn (weakenTerm p u) (weakenType p t)
{-# COMPILE AGDA2HS weakenTerm #-}

weakenSort p (STyp x) = STyp x
{-# COMPILE AGDA2HS weakenSort #-}

weakenType p (El st t) = El (weakenSort p st) (weakenTerm p t)
{-# COMPILE AGDA2HS weakenType #-}

weakenBranch p (BBranch c r x) = BBranch c r (weakenTerm (subExtScopeKeep r p) x)
{-# COMPILE AGDA2HS weakenBranch #-}

weakenBranches p BsNil         = BsNil
weakenBranches p (BsCons b bs) = BsCons (weakenBranch p b) (weakenBranches p bs)
{-# COMPILE AGDA2HS weakenBranches #-}

weakenTermS p ⌈⌉ = ⌈⌉
weakenTermS p (_ ↦ u ◂ e) = TSCons (weakenTerm p u) (weakenTermS p e)
{-# COMPILE AGDA2HS weakenTermS #-}

record Weaken (t : @0 Scope Name → Set) : Set where
  field
    weaken : α ⊆ β → t α → t β
open Weaken {{...}} public
{-# COMPILE AGDA2HS Weaken class #-}

instance
  iWeakenTerm : Weaken Term
  iWeakenTerm .weaken = weakenTerm
  iWeakenSort : Weaken Sort
  iWeakenSort .weaken = weakenSort
  iWeakenType : Weaken Type
  iWeakenType .weaken = weakenType
  iWeakenBranch : Weaken (λ α → Branch α c)
  iWeakenBranch .weaken = weakenBranch
  iWeakenBranches : Weaken (λ α → Branches α cs)
  iWeakenBranches .weaken = weakenBranches
  iWeakenTermS : Weaken (λ α → TermS α rβ)
  iWeakenTermS .weaken = weakenTermS
{-# COMPILE AGDA2HS iWeakenTerm #-}
{-# COMPILE AGDA2HS iWeakenSort #-}
{-# COMPILE AGDA2HS iWeakenType #-}
{-# COMPILE AGDA2HS iWeakenBranch #-}
{-# COMPILE AGDA2HS iWeakenBranches #-}
{-# COMPILE AGDA2HS iWeakenTermS #-}

raise : Rezz rγ → Term α → Term (extScope α rγ)
raise r = weakenTerm (subExtScope r subRefl)
{-# COMPILE AGDA2HS raise #-}

raiseType : {@0 α β : Scope Name} → Rezz β → Type α → Type (α <> β)
raiseType r = weakenType (subJoinDrop r subRefl)
{-# COMPILE AGDA2HS raiseType #-}

strengthenTerm : α ⊆ β → Term β → Maybe (Term α)
strengthenSort : α ⊆ β → Sort β → Maybe (Sort α)
strengthenType : α ⊆ β → Type β → Maybe (Type α)
strengthenBranch : α ⊆ β → Branch β c → Maybe (Branch α c)
strengthenBranches : α ⊆ β → Branches β cs → Maybe (Branches α cs)
strengthenTermS : α ⊆ β → TermS β rγ → Maybe (TermS α rγ)

strengthenTerm p (TVar (⟨ x ⟩ q)) = diffCase p q (λ q → Just (TVar (⟨ x ⟩ q))) (λ _ → Nothing)
strengthenTerm p (TDef d) = Just (TDef d)
strengthenTerm p (TData d ps is) = TData d <$> strengthenTermS p ps <*> strengthenTermS p is
strengthenTerm p (TCon c vs) = TCon c <$> strengthenTermS p vs
strengthenTerm p (TLam x v) = TLam x <$> strengthenTerm (subBindKeep p) v
strengthenTerm p (TApp v e) = TApp <$> strengthenTerm p v <*> strengthenTerm p e
strengthenTerm p (TProj u f) = (λ v → TProj v f) <$> strengthenTerm p u
strengthenTerm p (TCase d r u bs m) =
  TCase d r <$> strengthenTerm p u
            <*> strengthenBranches p bs
            <*> strengthenType (subBindKeep (subExtScopeKeep r p)) m
strengthenTerm p (TPi x a b) =
  TPi x <$> strengthenType p a <*> strengthenType (subBindKeep p) b
strengthenTerm p (TSort s) = TSort <$> strengthenSort p s
strengthenTerm p (TLet x u v) = TLet x <$> strengthenTerm p u <*> strengthenTerm (subBindKeep p) v
strengthenTerm p (TAnn u t) = TAnn <$> strengthenTerm p u <*> strengthenType p t

strengthenSort p (STyp n) = Just (STyp n)

strengthenType p (El st t) = El <$> strengthenSort p st <*> strengthenTerm p t

strengthenBranch p (BBranch c r v) = BBranch c r <$> strengthenTerm (subExtScopeKeep r p) v

strengthenBranches p BsNil = Just BsNil
strengthenBranches p (BsCons b bs) = BsCons <$> strengthenBranch p b <*> strengthenBranches p bs

strengthenTermS p ⌈⌉ = Just ⌈⌉
strengthenTermS p (x ↦ v ◂ vs) = TSCons <$> strengthenTerm p v <*> strengthenTermS p vs

{-# COMPILE AGDA2HS strengthenTerm #-}
{-# COMPILE AGDA2HS strengthenType #-}
{-# COMPILE AGDA2HS strengthenSort #-}
{-# COMPILE AGDA2HS strengthenBranch #-}
{-# COMPILE AGDA2HS strengthenBranches #-}
{-# COMPILE AGDA2HS strengthenTermS #-}

record Strengthen (t : @0 Scope Name → Set) : Set where
  field
    strengthen : α ⊆ β → t β → Maybe (t α)
open Strengthen {{...}} public
{-# COMPILE AGDA2HS Strengthen class #-}

instance
  iStrengthenTerm : Strengthen Term
  iStrengthenTerm .strengthen = strengthenTerm
  iStrengthenType : Strengthen Type
  iStrengthenType .strengthen = strengthenType
  iStrengthenSort : Strengthen Sort
  iStrengthenSort .strengthen = strengthenSort
  iStrengthenBranch : Strengthen (λ α → Branch α c)
  iStrengthenBranch .strengthen = strengthenBranch
  iStrengthenBranches : Strengthen (λ α → Branches α cs)
  iStrengthenBranches .strengthen = strengthenBranches
  iStrengthenTermS : Strengthen (λ α → TermS α rβ)
  iStrengthenTermS .strengthen = strengthenTermS

{-# COMPILE AGDA2HS iStrengthenTerm #-}
{-# COMPILE AGDA2HS iStrengthenType #-}
{-# COMPILE AGDA2HS iStrengthenSort #-}
{-# COMPILE AGDA2HS iStrengthenBranch #-}
{-# COMPILE AGDA2HS iStrengthenBranches #-}
{-# COMPILE AGDA2HS iStrengthenTermS #-}

opaque
  unfolding Scope
  liftBindListNameIn : List (NameIn (α ▸ x)) → List (NameIn α)
  liftBindListNameIn [] = []
  liftBindListNameIn ((⟨ x ⟩ (Zero ⟨ p ⟩)) ∷ l) = liftBindListNameIn l
  liftBindListNameIn ((⟨ x ⟩ (Suc n ⟨ IsSuc p ⟩)) ∷ l) = < n ⟨ p ⟩ > ∷ (liftBindListNameIn l)

  liftListNameIn : Rezz rγ → List (NameIn (extScope α rγ)) → List (NameIn α)
  liftListNameIn _ [] = []
  liftListNameIn {rγ = rγ} rγRun ((⟨ x ⟩ xInγα) ∷ l) =
    let @0 γ : Scope Name
        γ = extScope [] rγ
        @0 e : (extScope α rγ) ≡ γ ++ α
        e = extScopeConcatEmpty _ rγ
        γRun : Rezz γ
        γRun = rezzExtScope (rezz []) rγRun in
          (inJoinCase γRun (subst0 (λ β → _ ∈ β) e xInγα)
              (λ xInα → < xInα > ∷ (liftListNameIn rγRun l))
              (λ _ → liftListNameIn rγRun l))

{- TODO: create merge function for sorted lists of var as replacing <> by it would **greatly** decrease complexity -}
varInTerm : Term α → List (NameIn α)
varInTermS : TermS α rγ → List (NameIn α)
varInType : Type α → List (NameIn α)
varInBranches : Branches α cs → List (NameIn α)
varInBranch : Branch α c → List (NameIn α)

varInTerm (TVar x) = x ∷ []
varInTerm (TDef d) = []
varInTerm (TData d ps is) = varInTermS is <> (varInTermS ps)
varInTerm (TCon c vs) = varInTermS vs
varInTerm (TLam x v) = liftBindListNameIn (varInTerm v)
varInTerm (TApp t₀ t₁) = varInTerm t₀ <> (varInTerm t₁)
varInTerm (TProj t x) = varInTerm t
varInTerm (TCase d r u bs m) =
  varInTerm u <>
  (varInBranches bs) <>
  (liftListNameIn r (liftBindListNameIn (varInType m)))
varInTerm (TPi x a b) = varInType a <> (liftBindListNameIn (varInType b))
varInTerm (TSort x) = []
varInTerm (TLet x t t₁) = varInTerm t <> (liftBindListNameIn (varInTerm t₁))
varInTerm (TAnn u t) = varInTerm u <> varInType t

varInTermS ⌈⌉ = []
varInTermS (x ↦ u ◂ σ) = (varInTerm u) <> (varInTermS σ)

varInType (El _ u) = varInTerm u

varInBranches BsNil = []
varInBranches (BsCons b bs) = varInBranch b <> (varInBranches bs)

varInBranch (BBranch c r v) = liftListNameIn r (varInTerm v)
