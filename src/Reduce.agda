
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
open import Haskell.Extra.Erase
open import Haskell.Extra.Delay
open import Haskell.Prim.Thunk

import Syntax
import Substitute

module Reduce
  {@0 name  : Set}
  (@0 defs     : Scope name)
  (@0 cons     : Scope name)
  (@0 conArity : All (λ _ → Scope name) cons)
  where

open Syntax defs cons conArity
open Substitute defs cons conArity

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
  step (MkState e (TVar x p) s) = 
    case lookupEnvironment e p of λ where
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
  step (MkState e (TDef d q) s) = Nothing -- TODO
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
  step (MkState e (TPi x sa sb a b) s) = Nothing
  step (MkState e (TSort n) s) = Nothing
  step (MkState e (TAnn u t) s) = Just (MkState e u s) -- TODO preserve annotations on non-inferrable terms

{-# COMPILE AGDA2HS step #-}

-- TODO: make this into a `where` function once 
-- https://github.com/agda/agda2hs/issues/264 is fixed
reduceState : ∀ {@0 i} → Rezz _ α
            → State α → Delay (Term α) i
reduceState r s = case (step s) of λ where 
      (Just s') → later λ where .force → reduceState r s'
      Nothing   → now (unState r s)
{-# COMPILE AGDA2HS reduceState #-}

reduce : Rezz _ α
       → Term α → Delay (Term α) ∞
reduce {α = α} r v = reduceState r (makeState v)
{-# COMPILE AGDA2HS reduce #-}

reduceClosed : (v : Term mempty) → Delay (Term mempty) ∞
reduceClosed = reduce (rezz _)

{-# COMPILE AGDA2HS reduceClosed #-}




-- -}
-- -}
-- -}
