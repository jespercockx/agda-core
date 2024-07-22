open import Scope
open import Agda.Core.GlobalScope using (Globals; Name)

module Agda.Core.Syntax
  (@0 globals : Globals)
  where

private open module @0 G = Globals globals

open import Haskell.Prelude hiding (All; coerce; a; b; c)
open import Haskell.Law.Equality using (sym; subst0)
open import Haskell.Law.Monoid.Def using (leftIdentity; rightIdentity)
open import Haskell.Law.Semigroup.Def using (associativity)
open import Haskell.Prim.Tuple using (first)
open import Haskell.Extra.Erase

-- NOTE(flupe): comes from scope library, should be moved upstream probably
open import Utils.Misc

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
{-# COMPILE AGDA2HS Type #-}

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
  -- NOTE(flupe): removed tactic arguments for now because hidden arguments not supported yet #217
  TVar  : (@0 x : Name) → x ∈ α → Term α
  TDef  : (@0 d : Name) → d ∈ defScope → Term α
  TCon  : (@0 c : Name) (c∈cons : c ∈ conScope)
        → (lookupAll fieldScope c∈cons) ⇒ α → Term α
  TLam  : (@0 x : Name) (v : Term (x ◃ α)) → Term α
  TApp  : (u : Term α) (v : Term α) → Term α
  TProj : (u : Term α) (@0 x : Name) → x ∈ defScope → Term α
  TCase : (u : Term α) (bs : Branches α cs) (m : Type (x ◃ α)) → Term α
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
  BBranch : (@0 c : Name) → (c∈cons : c ∈ conScope)
          → Rezz _ (lookupAll fieldScope c∈cons)
          → Term (~ lookupAll fieldScope c∈cons <> α) → Branch α c
{-# COMPILE AGDA2HS Branch deriving Show #-}

data Branches α where
  BsNil : Branches α mempty
  BsCons : Branch α c → Branches α cs → Branches α (c ◃ cs)
{-# COMPILE AGDA2HS Branches #-}

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

rezzBranches : Branches α β → Rezz _ β
rezzBranches BsNil = rezz mempty
rezzBranches (BsCons {c = c} bh bt) = rezzCong (λ cs → c ◃ cs) (rezzBranches bt)

allBranches : Branches α β → All (λ c → c ∈ conScope) β
allBranches BsNil = allEmpty
allBranches (BsCons (BBranch _ ci _ _) bs) = allJoin (allSingl ci) (allBranches bs)

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

dataType : (@0 d : Name) → d ∈ defScope
         → Sort α
         → (pars : β ⇒ α)
         → (ixs : γ ⇒ α)
         → Type α
dataType d dp ds pars ixs = El ds (applySubst (applySubst (TDef d dp) pars) ixs)
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
unAppsView (TVar _ _) = refl
unAppsView (TDef _ _) = refl
unAppsView (TCon _ _ _) = refl
unAppsView (TProj _ _ _) = refl
unAppsView (TCase _ _ _) = refl
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

  caseSubstBind : (s : Subst (bind x α) β)
                → ((t : Term β) → (s' : Subst α β) → @0 {{s ≡ SCons t s'}} → d)
                → d
  caseSubstBind (SCons x s) f = f x s

  {-# COMPILE AGDA2HS caseSubstBind #-}

weaken         : α ⊆ β → Term α → Term β
weakenSort     : α ⊆ β → Sort α → Sort β
weakenType     : α ⊆ β → Type α → Type β
weakenBranch   : α ⊆ β → Branch α c → Branch β c
weakenBranches : α ⊆ β → Branches α cs → Branches β cs
weakenSubst    : β ⊆ γ → Subst α β → Subst α γ

weaken p (TVar x k)        = TVar x (coerce p k)
weaken p (TDef d k)        = TDef d k
weaken p (TCon c k vs)     = TCon c k (weakenSubst p vs)
weaken p (TLam x v)        = TLam x (weaken (subBindKeep p) v)
weaken p (TApp u e)        = TApp (weaken p u) (weaken p e)
weaken p (TProj u x k)     = TProj (weaken p u) x k
weaken p (TCase u bs m)    = TCase (weaken p u) (weakenBranches p bs) (weakenType (subBindKeep p) m)
weaken p (TPi x a b)       = TPi x (weakenType p a) (weakenType (subBindKeep p) b)
weaken p (TSort α)         = TSort (weakenSort p α)
weaken p (TLet x v t)      = TLet x (weaken p v) (weaken (subBindKeep p) t)
weaken p (TAnn u t)        = TAnn (weaken p u) (weakenType p t)
{-# COMPILE AGDA2HS weaken #-}

weakenSort p (STyp x) = STyp x
{-# COMPILE AGDA2HS weakenSort #-}

weakenType p (El st t) = El (weakenSort p st) (weaken p t)

weakenBranch p (BBranch c k r x) = BBranch c k r (weaken (subJoinKeep (rezzCong revScope r) p) x)
{-# COMPILE AGDA2HS weakenBranch #-}

weakenBranches p BsNil         = BsNil
weakenBranches p (BsCons b bs) = BsCons (weakenBranch p b) (weakenBranches p bs)
{-# COMPILE AGDA2HS weakenBranches #-}

weakenSubst p SNil = SNil
weakenSubst p (SCons u e) = SCons (weaken p u) (weakenSubst p e)
{-# COMPILE AGDA2HS weakenSubst #-}

dropSubst : {@0 α β : Scope Name} {@0 x : Name} → (x ◃ α) ⇒ β → α ⇒ β
dropSubst f = caseSubstBind f (λ _ g → g)
{-# COMPILE AGDA2HS dropSubst #-}

listSubst : {@0 β : Scope Name} → Rezz _ β → List (Term α) → Maybe ((β ⇒ α) × (List (Term α)))
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

opaque
  unfolding Scope Sub

  subToSubst : Rezz _ α → α ⊆ β → α ⇒ β
  subToSubst (rezz []) p = SNil
  subToSubst (rezz (Erased x ∷ α)) p =
    SCons (TVar x (coerce p inHere))
          (subToSubst (rezz α) (joinSubRight (rezz _) p))

opaque
  unfolding Scope revScope

  revSubstAcc : {@0 α β γ : Scope Name} → α ⇒ γ → β ⇒ γ → (revScopeAcc α β) ⇒ γ
  revSubstAcc SNil p = p
  revSubstAcc (SCons x s) p = revSubstAcc s (SCons x p)
  {-# COMPILE AGDA2HS revSubstAcc #-}

  revSubst : {@0 α β : Scope Name} → α ⇒ β → ~ α ⇒ β
  revSubst = flip revSubstAcc SNil
  {-# COMPILE AGDA2HS revSubst #-}

liftSubst : {@0 α β γ : Scope Name} → Rezz _ α → β ⇒ γ → (α <> β) ⇒ (α <> γ)
liftSubst r f =
  concatSubst (subToSubst r (subJoinHere r subRefl))
              (weakenSubst (subJoinDrop r subRefl) f)
{-# COMPILE AGDA2HS liftSubst #-}

idSubst : {@0 β : Scope Name} → Rezz _ β → β ⇒ β
idSubst r = subst0 (λ β → Subst β β) (rightIdentity _) (liftSubst r SNil)
{-# COMPILE AGDA2HS idSubst #-}

liftBindSubst : {@0 α β : Scope Name} {@0 x y : Name} → α ⇒ β → (bind x α) ⇒ (bind y β)
liftBindSubst {y = y} e = SCons (TVar y inHere) (weakenSubst (subBindDrop subRefl) e)
{-# COMPILE AGDA2HS liftBindSubst #-}

raiseSubst : {@0 α β : Scope Name} → Rezz _ β → α ⇒ β → (α <> β) ⇒ β
raiseSubst {β = β} r SNil = subst (λ α → α ⇒ β) (sym (leftIdentity β)) (idSubst r)
raiseSubst {β = β} r (SCons {α = α} u e) =
  subst (λ α → α ⇒ β)
    (associativity (singleton _) α β)
    (SCons u (raiseSubst r e))
{-# COMPILE AGDA2HS raiseSubst #-}

revIdSubst : {@0 α : Scope Name} → Rezz _ α → α ⇒ ~ α
revIdSubst {α} r = subst0 (λ s →  s ⇒ (~ α)) (revsInvolution α) (revSubst (idSubst (rezzCong revScope r)))

raise : {@0 α β : Scope Name} → Rezz _ α → Term β → Term (α <> β)
raise r = weaken (subJoinDrop r subRefl)
{-# COMPILE AGDA2HS raise #-}

raiseType : {@0 α β : Scope Name} → Rezz _ α → Type β → Type (α <> β)
raiseType r = weakenType (subJoinDrop r subRefl)
{-# COMPILE AGDA2HS raiseType #-}

strengthen : α ⊆ β → Term β → Maybe (Term α)
strengthenSort : α ⊆ β → Sort β → Maybe (Sort α)
strengthenType : α ⊆ β → Type β → Maybe (Type α)
strengthenBranch : α ⊆ β → Branch β c → Maybe (Branch α c)
strengthenBranches : α ⊆ β → Branches β cs → Maybe (Branches α cs)
strengthenSubst : α ⊆ β → γ ⇒ β → Maybe (γ ⇒ α)

strengthen p (TVar x q) = diffCase p q (λ q → Just (TVar x q)) (λ _ → Nothing)
strengthen p (TDef d q) = Just (TDef d q)
strengthen p (TCon c q vs) = TCon c q <$> strengthenSubst p vs
strengthen p (TLam x v) = TLam x <$> strengthen (subBindKeep p) v
strengthen p (TApp v e) = TApp <$> strengthen p v <*> strengthen p e
strengthen p (TProj u f q) = (λ v → TProj v f q) <$> strengthen p u
strengthen p (TCase u bs m) =
  TCase <$> strengthen p u <*> strengthenBranches p bs <*> strengthenType (subBindKeep p) m
strengthen p (TPi x a b) =
  TPi x <$> strengthenType p a <*> strengthenType (subBindKeep p) b
strengthen p (TSort s) = TSort <$> strengthenSort p s
strengthen p (TLet x u v) = TLet x <$> strengthen p u <*> strengthen (subBindKeep p) v
strengthen p (TAnn u t) = TAnn <$> strengthen p u <*> strengthenType p t

strengthenSort p (STyp n) = Just (STyp n)

strengthenType p (El st t) = El <$> strengthenSort p st <*> strengthen p t

strengthenBranch p (BBranch c q r v) = BBranch c q r <$> strengthen (subJoinKeep (rezzCong revScope r) p) v

strengthenBranches p BsNil = Just BsNil
strengthenBranches p (BsCons b bs) = BsCons <$> strengthenBranch p b <*> strengthenBranches p bs

strengthenSubst p SNil = Just SNil
strengthenSubst p (SCons v vs) = SCons <$> strengthen p v <*> strengthenSubst p vs
