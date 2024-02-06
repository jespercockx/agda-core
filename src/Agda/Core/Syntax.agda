open import Scope
open import Agda.Core.GlobalScope using (Globals)

module Agda.Core.Syntax
  {@0 name    : Set}
  (@0 globals : Globals name)
  where

private open module @0 G = Globals globals

open import Haskell.Prelude hiding (All; coerce; a; b; c)
open import Haskell.Law.Equality using (sym)
open import Haskell.Law.Monoid.Def using (leftIdentity)
open import Haskell.Law.Semigroup.Def using (associativity)
open import Haskell.Extra.Erase

-- NOTE(flupe): comes from scope library, should be moved upstream probably
open import Utils.Misc

private variable
  @0 x a b c : name
  @0 α β γ cs : Scope name

data Term   (@0 α : Scope name) : Set
data Sort   (@0 α : Scope name) : Set
record Type (@0 α : Scope name) : Set
data Elim   (@0 α : Scope name) : Set
data Branch (@0 α : Scope name) : @0 name → Set
Elims     : (@0 α : Scope name) → Set
data Branches (@0 α : Scope name) : @0 Scope name → Set

record Type α where
  inductive
  constructor El
  field
    typeSort : Sort α
    unType   : Term α
open Type public
{-# COMPILE AGDA2HS Type #-}

data Subst : (@0 α β : Scope name) → Set where
  SNil  : Subst mempty β
  SCons : Term β → Subst α β → Subst (x ◃ α) β
{-# COMPILE AGDA2HS Subst deriving Show #-}

syntax Subst α β = α ⇒ β

-- This should ideally be the following:
--   Subst α β = All (λ _ → Term β) α
-- but All being opaque prevents the positivity checker to do its job
-- see #6970

data Term α where
  -- NOTE(flupe): removed tactic arguments for now because hidden arguments not supported yet #217
  TVar  : (@0 x : name) → x ∈ α → Term α
  TDef  : (@0 d : name) → d ∈ defScope → Term α
  TCon  : (@0 c : name) (c∈cons : c ∈ conScope)
        → (lookupAll fieldScope c∈cons) ⇒ α → Term α
  TLam  : (@0 x : name) (v : Term (x ◃ α)) → Term α
  TApp  : (u : Term α) (es : Elim α) → Term α
  TPi   : (@0 x : name) (u : Type α) (v : Type (x ◃ α)) → Term α
  TSort : Sort α → Term α
  TLet  : (@0 x : name) (u : Term α) (v : Term (x ◃ α)) → Term α
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

data Elim α where
  EArg  : Term α → Elim α
  EProj : (@0 x : name) → x ∈ defScope → Elim α
  ECase : (bs : Branches α cs) → Elim α
  -- TODO: do we need a type annotation for the return type of case?
{-# COMPILE AGDA2HS Elim deriving Show #-}

Elims α = List (Elim α)
{-# COMPILE AGDA2HS Elims #-}

data Branch α where
  BBranch : (@0 c : name) → (c∈cons : c ∈ conScope)
          → Rezz _ (lookupAll fieldScope c∈cons)
          → Term (lookupAll fieldScope c∈cons <> α) → Branch α c
{-# COMPILE AGDA2HS Branch deriving Show #-}

data Branches α where
  BsNil : Branches α mempty
  BsCons : Branch α c → Branches α cs → Branches α (c ◃ cs)
{-# COMPILE AGDA2HS Branches #-}

apply : Term α → Term α → Term α
apply u v = TApp u (EArg v)
{-# COMPILE AGDA2HS apply #-}

applys : Term γ → (β ⇒ γ) → Term γ
applys {γ = γ} v SNil = v
applys {γ = γ} v (SCons u us) = applys (TApp v (EArg u)) us
{-# COMPILE AGDA2HS applys #-}

applyElims : Term α → Elims α → Term α
applyElims u []       = u
applyElims u (e ∷ es) = applyElims (TApp u e) es
{-# COMPILE AGDA2HS applyElims #-}

dataType : (@0 d : name) → d ∈ defScope
         → Sort α
         → (pars : β ⇒ α)
         → (ixs : γ ⇒ α)
         → Type α
dataType d dp ds pars ixs = El ds (applys (applys (TDef d dp) pars) ixs)
{-# COMPILE AGDA2HS dataType #-}

elimView : Term α → Term α × Elims α
elimView (TApp u es2) =
  case elimView u of λ where
    (u' , es1) → (u' , (es1 ++ es2 ∷ []))
elimView u = (u , [])
{-# COMPILE AGDA2HS elimView #-}

lookupSubst : α ⇒ β
            → (@0 x : name)
            → x ∈ α
            → Term β
lookupSubst SNil x q = inEmptyCase q
lookupSubst (SCons u f) x q = inBindCase q (λ _ → u) (lookupSubst f x)
{-# COMPILE AGDA2HS lookupSubst #-}

weaken         : α ⊆ β → Term α → Term β
weakenSort     : α ⊆ β → Sort α → Sort β
weakenType     : α ⊆ β → Type α → Type β
weakenElim     : α ⊆ β → Elim α → Elim β
weakenElims    : α ⊆ β → Elims α → Elims β
weakenBranch   : α ⊆ β → Branch α c → Branch β c
weakenBranches : α ⊆ β → Branches α cs → Branches β cs
weakenSubst    : β ⊆ γ → Subst α β → Subst α γ

weaken p (TVar x k)        = TVar x (coerce p k)
weaken p (TDef d k)        = TDef d k
weaken p (TCon c k vs)     = TCon c k (weakenSubst p vs)
weaken p (TLam x v)        = TLam x (weaken (subBindKeep p) v)
weaken p (TApp u e)        = TApp (weaken p u) (weakenElim p e)
weaken p (TPi x a b)       = TPi x (weakenType p a) (weakenType (subBindKeep p) b)
weaken p (TSort α)         = TSort (weakenSort p α)
weaken p (TLet x v t)      = TLet x (weaken p v) (weaken (subBindKeep p) t)
weaken p (TAnn u t)        = TAnn (weaken p u) (weakenType p t)
{-# COMPILE AGDA2HS weaken #-}

weakenSort p (STyp x) = STyp x
{-# COMPILE AGDA2HS weakenSort #-}

weakenType p (El st t) = El (weakenSort p st) (weaken p t)

weakenElim p (EArg x)    = EArg (weaken p x)
weakenElim p (EProj x k) = EProj x k
weakenElim p (ECase bs)  = ECase (weakenBranches p bs)
{-# COMPILE AGDA2HS weakenElim #-}

weakenElims p = map (weakenElim p)
{-# COMPILE AGDA2HS weakenElims #-}

weakenBranch p (BBranch c k r x) = BBranch c k r (weaken (subJoinKeep r p) x)
{-# COMPILE AGDA2HS weakenBranch #-}

weakenBranches p BsNil         = BsNil
weakenBranches p (BsCons b bs) = BsCons (weakenBranch p b) (weakenBranches p bs)
{-# COMPILE AGDA2HS weakenBranches #-}

weakenSubst p SNil = SNil
weakenSubst p (SCons u e) = SCons (weaken p u) (weakenSubst p e)
{-# COMPILE AGDA2HS weakenSubst #-}

opaque
  unfolding Scope Sub

  singleSubst : Term β → [ x ] ⇒ β
  singleSubst v = SCons v SNil

  idSubst : {@0 β : Scope name} → Rezz _ β → β ⇒ β
  idSubst (rezz [])      = SNil
  idSubst (rezz (x ∷ β)) = SCons (TVar (get x) inHere) (weakenSubst (subBindDrop subRefl) (idSubst (rezz β)))
  {-# COMPILE AGDA2HS idSubst #-}

  concatSubst : α ⇒ γ → β ⇒ γ → (α <> β) ⇒ γ
  concatSubst SNil q = q
  concatSubst (SCons v p) q = SCons v (concatSubst p q)

  liftSubst : {@0 α β γ : Scope name} → Rezz _ α → β ⇒ γ → (α <> β) ⇒ (α <> γ)
  liftSubst (rezz []) e = e
  liftSubst (rezz (x ∷ α)) e =
    SCons (TVar (get x) inHere)
          (weakenSubst (subBindDrop subRefl) (liftSubst (rezz α) e))
  {-# COMPILE AGDA2HS liftSubst #-}

  liftBindSubst : {@0 α β : Scope name} {@0 x y : name} → α ⇒ β → (bind x α) ⇒ (bind y β)
  liftBindSubst {y = y} e =
    SCons (TVar y inHere)
          (weakenSubst (subBindDrop subRefl) e)
  {-# COMPILE AGDA2HS liftBindSubst #-}

  coerceSubst : {@0 α β γ : Scope name} → Rezz _ α → α ⊆ β → β ⇒ γ → α ⇒ γ
  coerceSubst (rezz []) p e = SNil
  coerceSubst (rezz (x ∷ α)) p e =
    SCons (lookupSubst e _ (bindSubToIn p))
          (coerceSubst (rezz α) (joinSubRight (rezz [ get x ]) p) e)
  {-# COMPILE AGDA2HS coerceSubst #-}

  dropSubst : {@0 α β : Scope name} {@0 x : name} → (x ◃ α) ⇒ β → α ⇒ β
  dropSubst (SCons x f) = f
  {-# COMPILE AGDA2HS dropSubst #-}


opaque
  -- NOTE(flupe): I have to unfold Scope because otherwise the LawfulMonoid instance
  -- isn't related to the Semigroup definition
  unfolding Scope

  raiseSubst : {@0 α β : Scope name} → Rezz _ β → α ⇒ β → (α <> β) ⇒ β
  raiseSubst {β = β} r SNil = subst (λ α → α ⇒ β) (sym (leftIdentity β)) (idSubst r)
  raiseSubst {β = β} r (SCons {α = α} u e) =
    subst (λ α → α ⇒ β)
      (associativity (singleton _) α β)
      (SCons u (raiseSubst r e))
  {-# COMPILE AGDA2HS raiseSubst #-}

raise : {@0 α β : Scope name} → Rezz _ α → Term β → Term (α <> β)
raise r = weaken (subRight (splitRefl r))
{-# COMPILE AGDA2HS raise #-}

raiseType : {@0 α β : Scope name} → Rezz _ α → Type β → Type (α <> β)
raiseType r = weakenType (subRight (splitRefl r))
{-# COMPILE AGDA2HS raiseType #-}

strengthen : α ⊆ β → Term β → Maybe (Term α)
strengthenSort : α ⊆ β → Sort β → Maybe (Sort α)
strengthenType : α ⊆ β → Type β → Maybe (Type α)
strengthenElim : α ⊆ β → Elim β → Maybe (Elim α)
strengthenElims : α ⊆ β → Elims β → Maybe (Elims α)
strengthenBranch : α ⊆ β → Branch β c → Maybe (Branch α c)
strengthenBranches : α ⊆ β → Branches β cs → Maybe (Branches α cs)
strengthenSubst : α ⊆ β → γ ⇒ β → Maybe (γ ⇒ α)

strengthen p (TVar x q) = diffCase p q (λ q → Just (TVar x q)) (λ _ → Nothing)
strengthen p (TDef d q) = Just (TDef d q)
strengthen p (TCon c q vs) = TCon c q <$> strengthenSubst p vs
strengthen p (TLam x v) = TLam x <$> strengthen (subBindKeep p) v
strengthen p (TApp v e) = TApp <$> strengthen p v <*> strengthenElim p e
strengthen p (TPi x a b) =
  TPi x <$> strengthenType p a <*> strengthenType (subBindKeep p) b
strengthen p (TSort s) = TSort <$> strengthenSort p s
strengthen p (TLet x u v) = TLet x <$> strengthen p u <*> strengthen (subBindKeep p) v
strengthen p (TAnn u t) = TAnn <$> strengthen p u <*> strengthenType p t

strengthenSort p (STyp n) = Just (STyp n)

strengthenType p (El st t) = El <$> strengthenSort p st <*> strengthen p t

strengthenElim p (EArg v) = EArg <$> strengthen p v
strengthenElim p (EProj f q) = Just (EProj f q)
strengthenElim p (ECase bs) = ECase <$> strengthenBranches p bs

strengthenElims p = traverse (strengthenElim p)

strengthenBranch p (BBranch c q r v) = BBranch c q r <$> strengthen (subJoinKeep r p) v

strengthenBranches p BsNil = Just BsNil
strengthenBranches p (BsCons b bs) = BsCons <$> strengthenBranch p b <*> strengthenBranches p bs

strengthenSubst p SNil = Just SNil
strengthenSubst p (SCons v vs) = SCons <$> strengthen p v <*> strengthenSubst p vs
