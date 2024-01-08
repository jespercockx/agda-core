open import Haskell.Prelude hiding (All; coerce)
open import Haskell.Law.Equality using (sym)
open import Haskell.Law.Monoid.Def using (leftIdentity)
open import Haskell.Law.Semigroup.Def using (associativity)

open import Haskell.Extra.Erase

open import Utils.Misc

-- NOTE(flupe): make Scope export all of the following
open import Scope

module Syntax
  {@0 name     : Set}
  (@0 defs     : Scope name)
  (@0 cons     : Scope name)
  (@0 conArity : All (λ _ → Scope name) cons)
  where

private variable
  @0 x     : name
  @0 α β γ : Scope name

data Term   (@0 α : Scope name) : Set
data Sort   (@0 α : Scope name) : Set
data Elim   (@0 α : Scope name) : Set
data Branch (@0 α : Scope name) : Set
Elims     : (@0 α : Scope name) → Set
Branches  : (@0 α : Scope name) → Set

-- Design choice: no separate syntactic class for types. Everything
-- is just a term or a sort.
Type = Term
{-# COMPILE AGDA2HS Type #-}

data Subst : (@0 α β : Scope name) → Set where
  SNil  : Subst mempty β
  SCons : Term β → Subst α β → Subst (x ◃ α) β
{-# COMPILE AGDA2HS Subst #-}

syntax Subst α β = α ⇒ β

-- This should ideally be the following:
--   Subst α β = All (λ _ → Term β) α
-- but All being opaque prevents the positivity checker to do its job
-- see #6970

data Term α where
  -- NOTE(flupe): removed tactic arguments for now because hidden arguments not supported yet #217
  TVar  : (@0 x : name) → x ∈ α → Term α
  TDef  : (@0 d : name) → d ∈ defs → Term α
  TCon  : (@0 c : name) (c∈cons : c ∈ cons)
        → (lookupAll conArity c∈cons) ⇒ α → Term α
  TLam  : (@0 x : name) (v : Term (x ◃ α)) → Term α
  TApp  : (u : Term α) (es : Elim α) → Term α
  TPi   : (@0 x : name) (u : Term α) (v : Term (x ◃ α)) → Term α
  TSort : Sort α → Term α
  TLet  : (@0 x : name) (u : Term α) (v : Term (x ◃ α)) → Term α
  -- TODO: type annotations
  -- TODO: literals
  -- TODO: constructor for type annotation
{-# COMPILE AGDA2HS Term #-}

data Sort α where
  STyp : Nat → Sort α
  -- TODO: universe polymorphism
{-# COMPILE AGDA2HS Sort #-}

data Elim α where
  EArg  : Term α → Elim α
  EProj : (@0 x : name) → x ∈ defs → Elim α
  ECase : (bs : Branches α) → Elim α
  -- TODO: do we need a type annotation for the return type of case?
{-# COMPILE AGDA2HS Elim     #-}

Elims α = List (Elim α)
{-# COMPILE AGDA2HS Elims #-}

data Branch α where
  BBranch : (@0 c : name) → (c∈cons : c ∈ cons)
          → Rezz _ (lookupAll conArity c∈cons)
          → Term (lookupAll conArity c∈cons <> α) → Branch α
{-# COMPILE AGDA2HS Branch   #-}

Branches α = List (Branch α)
{-# COMPILE AGDA2HS Branches #-}

apply : Term α → Term α → Term α
apply u v = TApp u (EArg v)
{-# COMPILE AGDA2HS apply #-}

applyElims : Term α → Elims α → Term α
applyElims u []       = u
applyElims u (e ∷ es) = applyElims (TApp u e) es
{-# COMPILE AGDA2HS applyElims #-}

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
weakenElim     : α ⊆ β → Elim α → Elim β
weakenElims    : α ⊆ β → Elims α → Elims β
weakenBranch   : α ⊆ β → Branch α → Branch β
weakenBranches : α ⊆ β → Branches α → Branches β
weakenSubst    : β ⊆ γ → Subst α β → Subst α γ

weaken p (TVar x k)    = TVar x (coerce p k)
weaken p (TDef d k)    = TDef d k
weaken p (TCon c k vs) = TCon c k (weakenSubst p vs)
weaken p (TLam x v)    = TLam x (weaken (subBindKeep p) v)
weaken p (TApp u e)    = TApp (weaken p u) (weakenElim p e)
weaken p (TPi x a b)   = TPi x (weaken p a) (weaken (subBindKeep p) b)
weaken p (TSort α)     = TSort (weakenSort p α)
weaken p (TLet x v t)  = TLet x (weaken p v) (weaken (subBindKeep p) t)
{-# COMPILE AGDA2HS weaken #-}

weakenSort p (STyp x) = STyp x
{-# COMPILE AGDA2HS weakenSort #-}

weakenElim p (EArg x)    = EArg (weaken p x)
weakenElim p (EProj x k) = EProj x k
weakenElim p (ECase bs)  = ECase (weakenBranches p bs)
{-# COMPILE AGDA2HS weakenElim #-}

weakenElims p = map (weakenElim p)
{-# COMPILE AGDA2HS weakenElims #-}

weakenBranch p (BBranch c k r x) = BBranch c k r (weaken (subJoinKeep r p) x)
{-# COMPILE AGDA2HS weakenBranch #-}

weakenBranches p []       = []
weakenBranches p (b ∷ bs) = weakenBranch p b ∷ weakenBranches p bs
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

strengthen : α ⊆ β → Term β → Maybe (Term α)
strengthenSort : α ⊆ β → Sort β → Maybe (Sort α)
strengthenElim : α ⊆ β → Elim β → Maybe (Elim α)
strengthenElims : α ⊆ β → Elims β → Maybe (Elims α)
strengthenBranch : α ⊆ β → Branch β → Maybe (Branch α)
strengthenBranches : α ⊆ β → Branches β → Maybe (Branches α)
strengthenSubst : α ⊆ β → γ ⇒ β → Maybe (γ ⇒ α)

strengthen p (TVar x q) = diffCase p q (λ q → Just (TVar x q)) (λ _ → Nothing)
strengthen p (TDef d q) = Just (TDef d q)
strengthen p (TCon c q vs) = TCon c q <$> strengthenSubst p vs
strengthen p (TLam x v) = TLam x <$> strengthen (subBindKeep p) v
strengthen p (TApp v e) = TApp <$> strengthen p v <*> strengthenElim p e
strengthen p (TPi x a b) = TPi x <$> strengthen p a <*> strengthen (subBindKeep p) b
strengthen p (TSort s) = TSort <$> strengthenSort p s
strengthen p (TLet x u v) = TLet x <$> strengthen p u <*> strengthen (subBindKeep p) v

strengthenSort p (STyp n) = Just (STyp n)

strengthenElim p (EArg v) = EArg <$> strengthen p v
strengthenElim p (EProj f q) = Just (EProj f q)
strengthenElim p (ECase bs) = ECase <$> strengthenBranches p bs

strengthenElims p = traverse (strengthenElim p)

strengthenBranch p (BBranch c q r v) = BBranch c q r <$> strengthen (subJoinKeep r p) v

strengthenBranches p [] = Just []
strengthenBranches p (b ∷ bs) = _∷_ <$> strengthenBranch p b <*> strengthenBranches p bs

strengthenSubst p SNil = Just SNil
strengthenSubst p (SCons v vs) = SCons <$> strengthen p v <*> strengthenSubst p vs
