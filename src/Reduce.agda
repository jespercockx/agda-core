{-# OPTIONS --allow-unsolved-metas #-}

open import Scope.Core
open import Scope.Split
open import Scope.Sub
open import Scope.In
open import Scope.All

open import Utils.Dec
open import Utils.Either

open import Haskell.Prelude hiding (All)

module Reduce
  {@0 name  : Set}
  (@0 defs     : Scope name)
  (@0 cons     : Scope name)
  (conArity : All (λ _ → Scope name) cons) -- TODO: make this eraseable
  where

open import Syntax defs cons conArity
open import Substitute defs cons conArity
open import Utils.Erase

private variable
  @0 x     : name
  @0 α β γ : Scope name
  @0 u v w : Term α

data Environment : (α β : Scope name) → Set where
  []    : Environment α α
  _,_↦_ : Environment α β → (@0 x : name) → Term β → Environment α (x ◃ β)

envToSub : Environment α β → Sub α β
envToSub [] = subRefl
envToSub (e , x ↦ _) = subBindDrop (envToSub e)

envToLets : Environment α γ → Term γ → Term α
envToLets []            v = v
envToLets (env , x ↦ u) v = envToLets env (TLet x u v)

envToSubst : Rezz _ α → Environment α β → β ⇒ α
envToSubst r [] = idSubst r
envToSubst r (env , x ↦ v) =
  let s = envToSubst r env
  in  SCons (substTerm s v) s

record State (@0 α : Scope name) : Set where
  constructor state
  field
    @0 {fullScope}  : Scope name
    env : Environment α fullScope
    focus : Term fullScope
    stack : List (Elim fullScope)

open State

makeState : Term α → State α
makeState {α = α} v = state ([] {α = α}) v []

unState : Rezz _ α → State α → Term α
unState r (state e v s) = substTerm (envToSubst r e) (applyElims v s)

lookupBranch : Branches α → (@0 c : name) (p : c ∈ cons) → Maybe (Term ((lookupAll conArity p) <> α))
lookupBranch [] c k = Nothing
lookupBranch (BBranch c' k' aty u ∷ bs) c p =
  case decIn k' p of λ where
    (True  ⟨ refl ⟩) → Just u
    (False ⟨ _    ⟩) → lookupBranch bs c p

opaque
  unfolding Scope

  rezz-from-env : β ⇒ γ → Rezz _ β
  rezz-from-env SNil = rezz _
  rezz-from-env (SCons v vs) = rezzCong2 _∷_ rezzErase (rezz-from-env vs)

  extendEnvironment : β ⇒ γ → Environment α γ → Environment α (β <> γ)
  extendEnvironment vs e = go (rezz-from-env vs) vs e
    where
    go : Rezz _ β → β ⇒ γ → Environment α γ → Environment α (β <> γ)
    go r SNil e = e
    go r (SCons {α = α} v vs) e =
      let r' = rezzTail r
      in  go r' vs e , _ ↦ raise r' v

  lookupEnvironment : Environment α β → x ∈ β → Either (x ∈ α) (Term β)
  lookupEnvironment [] p = Left p
  lookupEnvironment (e , x ↦ v) p = inBindCase p
    (λ _ → Right (raise (rezz _) v))
    (λ p → mapRight (raise (rezz _)) (lookupEnvironment e p)) --mapEither (raise ?) (lookupEnvironment e p))

  step : (s : State α) → Maybe (State α)
  step (state e (TVar x p) s) = case lookupEnvironment e p of λ where
    (Left _) → Nothing
    (Right v) → Just (state e v s)
  step (state e (TApp v w) s) = Just (state e v (w ∷ s))
  step (state e (TLam x v) (EArg w ∷ s)) =
    Just (state
      (e , x ↦ w)
      v
      (weakenElims (subRight (splitRefl (rezz _))) s))
  step (state e (TLet x v w) s) =
    Just (state
      (e , x ↦ v)
      w
      (weakenElims (subRight (splitRefl (rezz _))) s))
  step (state e (TDef d q) s) = Nothing -- todo
  step (state e (TCon c q vs) (ECase bs ∷ s)) =
    case lookupBranch bs c q of λ where
      (Just v) → Just (state
        (extendEnvironment vs e)
        v
        (weakenElims (subRight (splitRefl (rezz _))) s))
      Nothing  → Nothing
  step (state e (TCon c q vs) (EProj f p ∷ s)) = Nothing -- TODO
  step (state e (TCon c q x) s) = Nothing
  step (state e (TLam x v) s) = Nothing
  step (state e (TPi x a b) s) = Nothing
  step (state e (TSort n) s) = Nothing

stepN : Nat → State α → Maybe (State α)
stepN zero _ = Nothing
stepN (suc n) s = case (step s) of λ where
  Nothing → Just s
  (Just s') → stepN n s'

reduce : Rezz _ α → Nat → Term α → Maybe (Term α)
reduce r n v = unState r <$> stepN n (makeState v)

reduceClosed : Nat → Term mempty → Maybe (Term mempty)
reduceClosed = reduce (rezz _)

{-


opaque
  unfolding Scope

  step : (α : Scope name) → Term α → Maybe (Term α)
  step α (TVar x _) = Nothing
  step α (TDef x _) = Nothing
  step α (TCon c _ vs) = Nothing
  step α (TLam x u) = Nothing
  step α (TApp u []) = step α u
  step α (TApp (TLam x u) (EArg v ∷ es)) = Just (substTop (rezz _) v u)
  step α (TApp (TCon c k us) (ECase bs ∷ es)) =
    case lookupBranch bs c k of λ where
      (Just v) → Just (substTerm (raiseEnv (rezz _) us) v) 
      Nothing  → Nothing
  step α (TApp u es) = fmap (λ u → TApp u es) (step α u)
  step α (TPi x a b) = Nothing
  step α (TSort x) = Nothing
  step α (TLet x u v) = case step α u of λ where
    (Just u') → Just (TLet x u' v)
    Nothing   → Just (substTop (rezz _) u v)
  {-# COMPILE AGDA2HS step #-}

{-
{-# TERMINATING #-}
reduce : {α : Scope name} (fuel : Nat) → Term α → Maybe (Term α)
reduce n u = 
  if n == 0
    then Nothing
    else λ ⦃ n≠0 ⦄ → case (step u) of λ where
      (Just u') → reduce (_-_ n 1 ⦃ {!!} ⦄) u'
      Nothing   → Just u
{-# COMPILE AGDA2HS reduce #-}
-}

-- -}
-- -}
-- -}
