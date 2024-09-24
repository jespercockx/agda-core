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

data Subst : (@0 α β : Scope Name) → Set where
  SNil  : Subst mempty β
  SCons : Term β → Subst α β → Subst (x ◃ α) β
{-# COMPILE AGDA2HS Subst deriving Show #-}

infix 5 Subst
syntax Subst α β = α ⇒ β

-- This should ideally be the following:
--   Subst α β = All (λ _ → Term β) α
-- but All being opaque prevents the positivity checker to do its job
-- see #6970

data Term α where
  TVar  : (x : NameIn α) → Term α
  TDef  : (d : NameIn defScope) → Term α
  TData : (d : NameIn dataScope)
        → (dataParScope d ⇒ α)
        → (dataIxScope d ⇒ α)
        → Term α
  TCon  : (c : NameIn conScope)
        → (fieldScope c ⇒ α) → Term α
  TLam  : (@0 x : Name) (v : Term (x ◃ α)) → Term α
  TApp  : (u : Term α) (v : Term α) → Term α
  TProj : (u : Term α) (x : NameIn defScope) → Term α
  TCase : (d : NameIn dataScope)                   -- Datatype of the variable we are splitting on
        → Rezz (dataIxScope d)                     -- Run-time representation of index scope
        → (u : Term α)                             -- Term we are casing on
        → (bs : Branches α cs)                     -- Branches (one for each constructor of d)
        → (m : Type (x ◃ (~ dataIxScope d <> α)))  -- Return type
        → Term α
  TPi   : (@0 x : Name) (u : Type α) (v : Type (x ◃ α)) → Term α
  TSort : Sort α → Term α
  TLet  : (@0 x : Name) (u : Term α) (v : Term (x ◃ α)) → Term α
  TAnn  : (u : Term α) (t : Type α) → Term α
  -- TODO: literals
{-# COMPILE AGDA2HS Term deriving Show #-}

data Sort α where
  STyp : Nat → Sort α
  -- TODO: universe polymorphism
{-# COMPILE AGDA2HS Sort deriving Show #-}

piSort : Sort α → Sort (x ◃ α) → Sort α
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
          → Term (~ fieldScope c <> α) → Branch α (proj₁ c)
{-# COMPILE AGDA2HS Branch deriving Show #-}

data Branches α where
  BsNil : Branches α mempty
  BsCons : Branch α c → Branches α cs → Branches α (c ◃ cs)
{-# COMPILE AGDA2HS Branches deriving Show #-}

opaque
  unfolding Scope

  caseBsNil : (bs : Branches α mempty)
            → (@0 {{bs ≡ BsNil}} → d)
            → d
  caseBsNil BsNil f = f
  {-# COMPILE AGDA2HS caseBsNil #-}

  caseBsCons : (bs : Branches α (c ◃ cs))
             → ((bh : Branch α c) (bt : Branches α cs) → @0 {{bs ≡ BsCons bh bt}} → d)
             → d
  caseBsCons (BsCons bh bt) f = f bh bt
  {-# COMPILE AGDA2HS caseBsCons #-}

rezzBranches : Branches α β → Rezz β
rezzBranches BsNil = rezz mempty
rezzBranches (BsCons {c = c} bh bt) = rezzCong (λ cs → c ◃ cs) (rezzBranches bt)
{-# COMPILE AGDA2HS rezzBranches #-}

allBranches : Branches α β → All (λ c → c ∈ conScope) β
allBranches BsNil = allEmpty
allBranches (BsCons (BBranch (⟨ _ ⟩ ci) _ _) bs) = allJoin (allSingl ci) (allBranches bs)
{-# COMPILE AGDA2HS allBranches #-}

apply : Term α → Term α → Term α
apply u v = TApp u v
{-# COMPILE AGDA2HS apply #-}

applys : Term γ → List (Term γ) → Term γ
applys {γ = γ} v [] = v
applys {γ = γ} v (u ∷ us) = applys (TApp v u) us
{-# COMPILE AGDA2HS applys #-}

applySubst : Term γ → (β ⇒ γ) → Term γ
applySubst {γ = γ} v SNil = v
applySubst {γ = γ} v (SCons u us) = applySubst (TApp v u) us
{-# COMPILE AGDA2HS applySubst #-}


dataTypeTerm : (d : NameIn dataScope)
         → (pars : dataParScope d ⇒ α)
         → (ixs : dataIxScope d ⇒ α)
         → Term α
dataTypeTerm d pars ixs = TData d pars ixs
{-# COMPILE AGDA2HS dataTypeTerm #-}

dataType : (d : NameIn dataScope)
         → Sort α
         → (pars : dataParScope d ⇒ α)
         → (ixs : dataIxScope d ⇒ α)
         → Type α
dataType d ds pars ixs = El ds (dataTypeTerm d pars ixs)
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

lookupSubst : α ⇒ β
            → (@0 x : Name)
            → x ∈ α
            → Term β
lookupSubst SNil x q = inEmptyCase q
lookupSubst (SCons u f) x q = inBindCase q (λ _ → u) (lookupSubst f x)

{-# COMPILE AGDA2HS lookupSubst #-}

opaque
  unfolding Scope

  caseSubstBind : (s : Subst (x ◃ α) β)
                → ((t : Term β) → (s' : Subst α β) → @0 {{s ≡ SCons t s'}} → d)
                → d
  caseSubstBind (SCons x s) f = f x s

  {-# COMPILE AGDA2HS caseSubstBind #-}

rezz~ : Rezz α → Rezz (~ α)
rezz~ = rezzCong revScope

{-# COMPILE AGDA2HS rezz~ inline #-}

rezz<> : Rezz α → Rezz β → Rezz (α <> β)
rezz<> = rezzCong2 _<>_

{-# COMPILE AGDA2HS rezz<> inline #-}

weakenTerm     : α ⊆ β → Term α → Term β
weakenSort     : α ⊆ β → Sort α → Sort β
weakenType     : α ⊆ β → Type α → Type β
weakenBranch   : α ⊆ β → Branch α c → Branch β c
weakenBranches : α ⊆ β → Branches α cs → Branches β cs
weakenSubst    : β ⊆ γ → Subst α β → Subst α γ

weakenTerm p (TVar (⟨ x ⟩ k))  = TVar (⟨ x ⟩ coerce p k)
weakenTerm p (TDef d)          = TDef d
weakenTerm p (TData d ps is)   = TData d (weakenSubst p ps) (weakenSubst p is)
weakenTerm p (TCon c vs)       = TCon c (weakenSubst p vs)
weakenTerm p (TLam x v)        = TLam x (weakenTerm (subBindKeep p) v)
weakenTerm p (TApp u e)        = TApp (weakenTerm p u) (weakenTerm p e)
weakenTerm p (TProj u x)       = TProj (weakenTerm p u) x
weakenTerm p (TCase d r u bs m) = TCase d r (weakenTerm p u) (weakenBranches p bs) (weakenType (subBindKeep (subJoinKeep (rezz~ r) p)) m)
weakenTerm p (TPi x a b)       = TPi x (weakenType p a) (weakenType (subBindKeep p) b)
weakenTerm p (TSort α)         = TSort (weakenSort p α)
weakenTerm p (TLet x v t)      = TLet x (weakenTerm p v) (weakenTerm (subBindKeep p) t)
weakenTerm p (TAnn u t)        = TAnn (weakenTerm p u) (weakenType p t)
{-# COMPILE AGDA2HS weakenTerm #-}

weakenSort p (STyp x) = STyp x
{-# COMPILE AGDA2HS weakenSort #-}

weakenType p (El st t) = El (weakenSort p st) (weakenTerm p t)
{-# COMPILE AGDA2HS weakenType #-}

weakenBranch p (BBranch c r x) = BBranch c r (weakenTerm (subJoinKeep (rezz~ r) p) x)
{-# COMPILE AGDA2HS weakenBranch #-}

weakenBranches p BsNil         = BsNil
weakenBranches p (BsCons b bs) = BsCons (weakenBranch p b) (weakenBranches p bs)
{-# COMPILE AGDA2HS weakenBranches #-}

weakenSubst p SNil = SNil
weakenSubst p (SCons u e) = SCons (weakenTerm p u) (weakenSubst p e)
{-# COMPILE AGDA2HS weakenSubst #-}

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
  iWeakenSubst : Weaken (Subst β)
  iWeakenSubst .weaken = weakenSubst
{-# COMPILE AGDA2HS iWeakenTerm #-}
{-# COMPILE AGDA2HS iWeakenSort #-}
{-# COMPILE AGDA2HS iWeakenType #-}
{-# COMPILE AGDA2HS iWeakenBranch #-}
{-# COMPILE AGDA2HS iWeakenBranches #-}
{-# COMPILE AGDA2HS iWeakenSubst #-}


dropSubst : {@0 α β : Scope Name} {@0 x : Name} → (x ◃ α) ⇒ β → α ⇒ β
dropSubst f = caseSubstBind f (λ _ g → g)
{-# COMPILE AGDA2HS dropSubst #-}

listSubst : {@0 β : Scope Name} → Rezz β → List (Term α) → Maybe ((β ⇒ α) × (List (Term α)))
listSubst (rezz β) [] =
  caseScope β
    (λ where {{refl}} → Just (SNil , []))
    (λ _ _ → Nothing)
listSubst (rezz β) (v ∷ vs) =
  caseScope β
    (λ where {{refl}} → Just (SNil , v ∷ vs))
    (λ where x γ {{refl}} → first (SCons v) <$> listSubst (rezzUnbind (rezz β)) vs)
{-# COMPILE AGDA2HS listSubst #-}

concatSubst : α ⇒ γ → β ⇒ γ → (α <> β) ⇒ γ
concatSubst SNil q =
  subst0 (λ α → Subst α _) (sym (leftIdentity _)) q
concatSubst (SCons v p) q =
  subst0 (λ α → Subst α _) (associativity _ _ _) (SCons v (concatSubst p q))

{-# COMPILE AGDA2HS concatSubst #-}

opaque
  unfolding Scope Sub

  subToSubst : Rezz α → α ⊆ β → α ⇒ β
  subToSubst (rezz []) p = SNil
  subToSubst (rezz (Erased x ∷ α)) p =
    SCons (TVar (⟨ x ⟩ coerce p inHere))
          (subToSubst (rezz α) (joinSubRight (rezz _) p))

{-# COMPILE AGDA2HS subToSubst #-}

opaque
  unfolding Scope revScope

  revSubstAcc : {@0 α β γ : Scope Name} → α ⇒ γ → β ⇒ γ → (revScopeAcc α β) ⇒ γ
  revSubstAcc SNil p = p
  revSubstAcc (SCons x s) p = revSubstAcc s (SCons x p)
  {-# COMPILE AGDA2HS revSubstAcc #-}

  revSubst : {@0 α β : Scope Name} → α ⇒ β → ~ α ⇒ β
  revSubst = flip revSubstAcc SNil
  {-# COMPILE AGDA2HS revSubst #-}

liftSubst : {@0 α β γ : Scope Name} → Rezz α → β ⇒ γ → (α <> β) ⇒ (α <> γ)
liftSubst r f =
  concatSubst (subToSubst r (subJoinHere r subRefl))
              (weakenSubst (subJoinDrop r subRefl) f)
{-# COMPILE AGDA2HS liftSubst #-}

idSubst : {@0 β : Scope Name} → Rezz β → β ⇒ β
idSubst r = subst0 (λ β → Subst β β) (rightIdentity _) (liftSubst r SNil)
{-# COMPILE AGDA2HS idSubst #-}

liftBindSubst : {@0 α β : Scope Name} {@0 x y : Name} → α ⇒ β → (bind x α) ⇒ (bind y β)
liftBindSubst {y = y} e = SCons (TVar (⟨ y ⟩ inHere)) (weakenSubst (subBindDrop subRefl) e)
{-# COMPILE AGDA2HS liftBindSubst #-}

raiseSubst : {@0 α β : Scope Name} → Rezz β → α ⇒ β → (α <> β) ⇒ β
raiseSubst {β = β} r SNil = subst (λ α → α ⇒ β) (sym (leftIdentity β)) (idSubst r)
raiseSubst {β = β} r (SCons {α = α} u e) =
  subst (λ α → α ⇒ β)
    (associativity (singleton _) α β)
    (SCons u (raiseSubst r e))
{-# COMPILE AGDA2HS raiseSubst #-}

revIdSubst : {@0 α : Scope Name} → Rezz α → α ⇒ ~ α
revIdSubst {α} r = subst0 (λ s →  s ⇒ (~ α)) (revsInvolution α) (revSubst (idSubst (rezz~ r)))
{-# COMPILE AGDA2HS revIdSubst #-}

raise : {@0 α β : Scope Name} → Rezz α → Term β → Term (α <> β)
raise r = weakenTerm (subJoinDrop r subRefl)
{-# COMPILE AGDA2HS raise #-}

raiseType : {@0 α β : Scope Name} → Rezz α → Type β → Type (α <> β)
raiseType r = weakenType (subJoinDrop r subRefl)
{-# COMPILE AGDA2HS raiseType #-}

strengthenTerm : α ⊆ β → Term β → Maybe (Term α)
strengthenSort : α ⊆ β → Sort β → Maybe (Sort α)
strengthenType : α ⊆ β → Type β → Maybe (Type α)
strengthenBranch : α ⊆ β → Branch β c → Maybe (Branch α c)
strengthenBranches : α ⊆ β → Branches β cs → Maybe (Branches α cs)
strengthenSubst : α ⊆ β → γ ⇒ β → Maybe (γ ⇒ α)

strengthenTerm p (TVar (⟨ x ⟩ q)) = diffCase p q (λ q → Just (TVar (⟨ x ⟩ q))) (λ _ → Nothing)
strengthenTerm p (TDef d) = Just (TDef d)
strengthenTerm p (TData d ps is) = TData d <$> strengthenSubst p ps <*> strengthenSubst p is
strengthenTerm p (TCon c vs) = TCon c <$> strengthenSubst p vs
strengthenTerm p (TLam x v) = TLam x <$> strengthenTerm (subBindKeep p) v
strengthenTerm p (TApp v e) = TApp <$> strengthenTerm p v <*> strengthenTerm p e
strengthenTerm p (TProj u f) = (λ v → TProj v f) <$> strengthenTerm p u
strengthenTerm p (TCase d r u bs m) =
  TCase d r <$> strengthenTerm p u
            <*> strengthenBranches p bs
            <*> strengthenType (subBindKeep (subJoinKeep (rezz~ r) p)) m
strengthenTerm p (TPi x a b) =
  TPi x <$> strengthenType p a <*> strengthenType (subBindKeep p) b
strengthenTerm p (TSort s) = TSort <$> strengthenSort p s
strengthenTerm p (TLet x u v) = TLet x <$> strengthenTerm p u <*> strengthenTerm (subBindKeep p) v
strengthenTerm p (TAnn u t) = TAnn <$> strengthenTerm p u <*> strengthenType p t

strengthenSort p (STyp n) = Just (STyp n)

strengthenType p (El st t) = El <$> strengthenSort p st <*> strengthenTerm p t

strengthenBranch p (BBranch c r v) = BBranch c r <$> strengthenTerm (subJoinKeep (rezz~ r) p) v

strengthenBranches p BsNil = Just BsNil
strengthenBranches p (BsCons b bs) = BsCons <$> strengthenBranch p b <*> strengthenBranches p bs

strengthenSubst p SNil = Just SNil
strengthenSubst p (SCons v vs) = SCons <$> strengthenTerm p v <*> strengthenSubst p vs

{-# COMPILE AGDA2HS strengthenTerm #-}
{-# COMPILE AGDA2HS strengthenType #-}
{-# COMPILE AGDA2HS strengthenSort #-}
{-# COMPILE AGDA2HS strengthenBranch #-}
{-# COMPILE AGDA2HS strengthenBranches #-}
{-# COMPILE AGDA2HS strengthenSubst #-}

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
  iStrengthenSubst : Strengthen (Subst α)
  iStrengthenSubst .strengthen = strengthenSubst

{-# COMPILE AGDA2HS iStrengthenTerm #-}
{-# COMPILE AGDA2HS iStrengthenType #-}
{-# COMPILE AGDA2HS iStrengthenSort #-}
{-# COMPILE AGDA2HS iStrengthenBranch #-}
{-# COMPILE AGDA2HS iStrengthenBranches #-}
{-# COMPILE AGDA2HS iStrengthenSubst #-}
