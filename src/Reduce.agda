{-# OPTIONS --allow-unsolved-metas #-}

open import Scope.Core
open import Scope.Split
open import Scope.Sub
open import Scope.In
open import Scope.All

open import Haskell.Extra.Dec
open import Haskell.Extra.Loop
open import Haskell.Extra.Refinement
open import Utils.Either

open import Haskell.Prelude hiding (All; coerce)

module Reduce
  {@0 name  : Set}
  (@0 defs     : Scope name)
  (@0 cons     : Scope name)
  (@0 conArity : All (λ _ → Scope name) cons)
  where

open import Syntax defs cons conArity
open import Substitute defs cons conArity
open import Haskell.Extra.Erase

private variable
  @0 x     : name
  @0 α β γ : Scope name
  @0 u v w : Term α

data Environment : (@0 α β : Scope name) → Set where
  EnvNil  : Environment α α
  EnvCons : Environment α β → (@0 x : name) → Term β → Environment α (x ◃ β)

{-# COMPILE AGDA2HS Environment #-}

syntax EnvCons e x v = e , x ↦ v

envToSub : Environment α β → Sub α β
envToSub EnvNil      = subRefl
envToSub (e , x ↦ _) = subBindDrop (envToSub e)

{-# COMPILE AGDA2HS envToSub #-}

envToLets : Environment α γ → Term γ → Term α
envToLets EnvNil        v = v
envToLets (env , x ↦ u) v = envToLets env (TLet x u v)

{-# COMPILE AGDA2HS envToLets #-}

envToSubst : Rezz _ α → Environment α β → β ⇒ α
envToSubst r EnvNil = idSubst r
envToSubst r (env , x ↦ v) =
  let s = envToSubst r env
  in  SCons (substTerm s v) s

{-# COMPILE AGDA2HS envToSubst #-}

record State (@0 α : Scope name) : Set where
  constructor MkState
  field
    @0 {fullScope}  : Scope name
    env : Environment α fullScope
    focus : Term fullScope
    stack : List (Elim fullScope)

open State public

{-# COMPILE AGDA2HS State #-}

makeState : Term α → State α
makeState {α = α} v = MkState (EnvNil {α = α}) v []

{-# COMPILE AGDA2HS makeState #-}

unState : Rezz _ α → State α → Term α
unState r (MkState e v s) = substTerm (envToSubst r e) (applyElims v s)

{-# COMPILE AGDA2HS unState #-}

lookupBranch : Branches α → (@0 c : name) (p : c ∈ cons)
             → Maybe ( Rezz _ (lookupAll conArity p)
                     × Term ((lookupAll conArity p) <> α))
lookupBranch [] c k = Nothing
lookupBranch (BBranch c' k' aty u ∷ bs) c p =
  case decIn k' p of λ where
    (True  ⟨ refl ⟩) → Just (aty , u)
    (False ⟨ _    ⟩) → lookupBranch bs c p

{-# COMPILE AGDA2HS lookupBranch #-}

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
  lookupEnvironment EnvNil      p = Left p
  lookupEnvironment (e , x ↦ v) p = inBindCase p
    (λ _ → Right (raise (rezz _) v))
    (λ p → mapRight (raise (rezz _)) (lookupEnvironment e p)) --mapEither (raise ?) (lookupEnvironment e p))

  step : (s : State α) → Maybe (State α)
  step (MkState e (TVar x p) s) = case lookupEnvironment e p of λ where
    (Left _) → Nothing
    (Right v) → Just (MkState e v s)
  step (MkState e (TApp v w) s) = Just (MkState e v (w ∷ s))
  step (MkState e (TLam x v) (EArg w ∷ s)) =
    Just (MkState
      (e , x ↦ w)
      v
      (weakenElims (subRight (splitRefl (rezz _))) s))
  step (MkState e (TLet x v w) s) =
    Just (MkState
      (e , x ↦ v)
      w
      (weakenElims (subRight (splitRefl (rezz _))) s))
  step (MkState e (TDef d q) s) = Nothing -- todo
  step (MkState e (TCon c q vs) (ECase bs ∷ s)) =
    case lookupBranch bs c q of λ where
      (Just (r , v)) → Just (MkState
        (extendEnvironment vs e)
        v
        (weakenElims (subRight (splitRefl r)) s))
      Nothing  → Nothing
  step (MkState e (TCon c q vs) (EProj f p ∷ s)) = Nothing -- TODO
  step (MkState e (TCon c q x) s) = Nothing
  step (MkState e (TLam x v) s) = Nothing
  step (MkState e (TPi x a b) s) = Nothing
  step (MkState e (TSort n) s) = Nothing

stepEither : State α → Either (State α) (State α)
stepEither s = case step s of λ where
  Nothing   → Right s
  (Just s') → Left s'

reduceS : Rezz _ α → (v : State α) → @0 Fuel stepEither (Left v) → State α
reduceS r v fuel = loop stepEither v fuel

reduce : Rezz _ α → (v : Term α) → @0 Fuel stepEither (Left (makeState v)) → Term α
reduce r v fuel = unState r (reduceS r (makeState v) fuel)

reduceClosed : (v : Term mempty) → @0 Fuel stepEither (Left (makeState v)) → Term mempty
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
