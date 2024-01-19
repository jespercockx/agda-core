open import Scope
open import Agda.Core.GlobalScope using (Globals)

module Agda.Core.Reduce
  {@0 name    : Set}
  (@0 globals : Globals name)
  where

open import Haskell.Prelude hiding (All; coerce)
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
open import Haskell.Extra.Erase
open import Utils.Either

open import Agda.Core.Syntax globals
open import Agda.Core.Substitute globals

private open module @0 G = Globals globals

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

lookupBranch : Branches α → (@0 c : name) (p : c ∈ conScope)
             → Maybe ( Rezz _ (lookupAll fieldScope p)
                     × Term ((lookupAll fieldScope p) <> α))
lookupBranch [] c k = Nothing
lookupBranch (BBranch c' k' aty u ∷ bs) c p =
  case decIn k' p of λ where
    (True  ⟨ refl ⟩) → Just (aty , u)
    (False ⟨ _    ⟩) → lookupBranch bs c p

{-# COMPILE AGDA2HS lookupBranch #-}

opaque
  unfolding Scope

  rezzFromEnv : β ⇒ γ → Rezz _ β
  rezzFromEnv SNil = rezz _
  rezzFromEnv (SCons v vs) = rezzCong2 _∷_ rezzErase (rezzFromEnv vs)

  {-# COMPILE AGDA2HS rezzFromEnv #-}

  -- TODO: make this into a where function once 
  -- https://github.com/agda/agda2hs/issues/264 is fixed.
  extendEnvironmentAux : Rezz _ β → β ⇒ γ → Environment α γ → Environment α (β <> γ)
  extendEnvironmentAux r SNil e = e
  extendEnvironmentAux r (SCons {α = α} v vs) e =
    let r' = rezzTail r
    in  extendEnvironmentAux r' vs e , _ ↦ raise r' v

  {-# COMPILE AGDA2HS extendEnvironmentAux #-}

  extendEnvironment : β ⇒ γ → Environment α γ → Environment α (β <> γ)
  extendEnvironment vs e = extendEnvironmentAux (rezzFromEnv vs) vs e

  {-# COMPILE AGDA2HS extendEnvironment #-}

  lookupEnvironment : Environment α β → x ∈ β → Either (x ∈ α) (Term β)
  lookupEnvironment EnvNil      p = Left p
  lookupEnvironment (e , x ↦ v) p = inBindCase p
    (λ _ → Right (raise (rezz _) v))
    (λ p → mapRight (raise (rezz _)) (lookupEnvironment e p))

  {-# COMPILE AGDA2HS lookupEnvironment #-}

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

data Fuel : Set where
  None : Fuel
  More : Fuel → Fuel

{-# COMPILE AGDA2HS Fuel #-}

-- TODO: make this into a `where` function once 
-- https://github.com/agda/agda2hs/issues/264 is fixed
reduceState : Rezz _ α
            → (s : State α) → Fuel → Maybe (Term α)
reduceState r s None        = Nothing
reduceState r s (More fuel) = case (step s) of λ where 
      (Just s') → reduceState r s' fuel
      Nothing   → Just (unState r s)
{-# COMPILE AGDA2HS reduceState #-}

reduce : Rezz _ α
       → (v : Term α) → Fuel → Maybe (Term α)
reduce {α = α} r v = reduceState r (makeState v)
{-# COMPILE AGDA2HS reduce #-}

reduceClosed : (v : Term mempty) → Fuel → Maybe (Term mempty)
reduceClosed = reduce (rezz _)

{-# COMPILE AGDA2HS reduceClosed #-}

ReducesTo : (v w : Term α) → Set
ReducesTo {α = α} v w = 
  ∃ (Rezz _ α) λ r    → 
  ∃ Fuel       λ fuel → 
  reduce r v fuel ≡ Just w


-- -}
-- -}
-- -}
