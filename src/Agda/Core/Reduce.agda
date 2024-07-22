open import Scope
open import Agda.Core.GlobalScope using (Globals; Name)

module Agda.Core.Reduce
  (@0 globals : Globals)
  where

open import Haskell.Prelude hiding (All; coerce; _,_,_; c) renaming (_,_ to infixr 5 _,_)
open import Haskell.Extra.Dec
open import Haskell.Extra.Refinement
open import Haskell.Extra.Erase
open import Haskell.Law.Equality
open import Haskell.Law.Monoid
open import Utils.Either

open import Agda.Core.Syntax globals
open import Agda.Core.Substitute globals
open import Agda.Core.Signature globals
open import Agda.Core.Utils

private open module @0 G = Globals globals

private variable
  @0 x c      : Name
  @0 α β γ cs : Scope Name
  @0 u v w    : Term α

data Environment : (@0 α β : Scope Name) → Set where
  EnvNil  : Environment α α
  EnvCons : Environment α β → (@0 x : Name) → Term β → Environment α (x ◃ β)

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

data Frame (@0 α : Scope Name) : Set where
  FApp  : (u : Term α) → Frame α
  FProj : (@0 x : Name) → x ∈ defScope → Frame α
  FCase : (bs : Branches α cs) (m : Type (x ◃ α)) → Frame α

unFrame : Frame α → Term α → Term α
unFrame (FApp v) u = TApp u v
unFrame (FProj f p) u = TProj u f p
unFrame (FCase bs m) u = TCase u bs m

weakenFrame : α ⊆ β → Frame α → Frame β
weakenFrame s (FApp u) = FApp (weaken s u)
weakenFrame s (FProj u f) = FProj u f
weakenFrame s (FCase bs m) = FCase (weakenBranches s bs) (weakenType (subBindKeep s) m)

Stack : (@0 α : Scope Name) → Set
Stack α = List (Frame α)

unStack : Stack α → Term α → Term α
unStack [] u = u
unStack (f ∷ fs) u = unStack fs (unFrame f u)

weakenStack : α ⊆ β → Stack α → Stack β
weakenStack s [] = []
weakenStack s (f ∷ fs) = weakenFrame s f ∷ weakenStack s fs

record State (@0 α : Scope Name) : Set where
  constructor MkState
  field
    @0 {fullScope}  : Scope Name
    env : Environment α fullScope
    focus : Term fullScope
    stack : Stack fullScope

open State public

{-# COMPILE AGDA2HS State #-}

makeState : Term α → State α
makeState {α = α} v = MkState (EnvNil {α = α}) v []

{-# COMPILE AGDA2HS makeState #-}

unState : Rezz _ α → State α → Term α
unState r (MkState e v s) = substTerm (envToSubst r e) (unStack s v)

{-# COMPILE AGDA2HS unState #-}

lookupBranch : Branches α cs → (@0 c : Name) (p : c ∈ conScope)
             → Maybe ( Rezz _ (lookupAll fieldScope p)
                     × Term (~ lookupAll fieldScope p <> α))
lookupBranch BsNil c k = Nothing
lookupBranch (BsCons (BBranch c' k' aty u) bs) c p =
  case decIn k' p of λ where
    (True  ⟨ refl ⟩) → Just (aty , u)
    (False ⟨ _    ⟩) → lookupBranch bs c p

{-# COMPILE AGDA2HS lookupBranch #-}

rezzFromEnv : β ⇒ γ → Rezz _ β
rezzFromEnv SNil = rezz _
rezzFromEnv (SCons v vs) = rezzCong2 (λ (Erased x) α → x ◃ α) rezzErase (rezzFromEnv vs)
{-# COMPILE AGDA2HS rezzFromEnv #-}

-- TODO: make this into a where function once
-- https://github.com/agda/agda2hs/issues/264 is fixed.
extendEnvironmentAux : Rezz _ β → β ⇒ γ → Environment α γ → Environment α (β <> γ)
extendEnvironmentAux r SNil e = subst0 (Environment _) (sym (leftIdentity _)) e
extendEnvironmentAux r (SCons {α = α} {x = x} v vs) e =
  let r' = rezzUnbind r
  in  subst0 (Environment _) (associativity _ _ _)
      (extendEnvironmentAux r' vs e , x ↦ raise r' v) --extendEnvironmentAux r' vs e , _ ↦ raise r' v
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

step : (sig : Signature) (s : State α) → Maybe (State α)
step sig (MkState e (TVar x p) s) =
  case lookupEnvironment e p of λ where
    (Left _) → Nothing
    (Right v) → Just (MkState e v s)
step sig (MkState e (TApp v w) s) = Just (MkState e v (FApp w ∷ s))
step sig (MkState e (TProj v f p) s) = Just (MkState e v (FProj f p ∷ s))
step sig (MkState e (TCase v bs m) s) = Just (MkState e v (FCase bs m ∷ s))
step sig (MkState e (TLam x v) (FApp w ∷ s)) =
  Just (MkState
    (e , x ↦ w)
    v
    (weakenStack (subBindDrop subRefl) s))
step sig (MkState e (TLet x v w) s) =
  Just (MkState
    (e , x ↦ v)
    w
    (weakenStack (subBindDrop subRefl) s))
step sig (MkState e (TDef d q) s) = case getBody sig d q of λ where
  (Just v) → Just (MkState e (weaken subEmpty v) s)
  Nothing  → Nothing
step sig (MkState e (TCon c q vs) (FCase bs _ ∷ s)) =
  case lookupBranch bs c q of λ where
    (Just (r , v)) → Just (MkState
      (extendEnvironment (revSubst vs) e)
      v
      (weakenStack (subJoinDrop (rezzCong revScope r) subRefl) s))
    Nothing  → Nothing
step sig (MkState e (TCon c q vs) (FProj f p ∷ s)) = Nothing -- TODO
step sig (MkState e (TCon c q x) s) = Nothing
step sig (MkState e (TLam x v) s) = Nothing
step sig (MkState e (TPi x a b) s) = Nothing
step sig (MkState e (TSort n) s) = Nothing
step sig (MkState e (TAnn u t) s) = Just (MkState e u s) -- TODO preserve annotations on non-inferrable terms

{-# COMPILE AGDA2HS step #-}

-- TODO: make this into a `where` function once
-- https://github.com/agda/agda2hs/issues/264 is fixed
reduceState : Rezz _ α
            → (sig : Signature) (s : State α) → Fuel → Maybe (Term α)
reduceState r sig s None        = Nothing
reduceState r sig s (More fuel) = case (step sig s) of λ where
      (Just s') → reduceState r sig s' fuel
      Nothing   → Just (unState r s)
{-# COMPILE AGDA2HS reduceState #-}

reduce : Rezz _ α
       → (sig : Signature) (v : Term α) → Fuel → Maybe (Term α)
reduce {α = α} r sig v = reduceState r sig (makeState v)
{-# COMPILE AGDA2HS reduce #-}

reduceClosed : (sig : Signature) (v : Term mempty) → Fuel → Maybe (Term mempty)
reduceClosed = reduce (rezz _)

{-# COMPILE AGDA2HS reduceClosed #-}

ReducesTo : (sig : Signature) (v w : Term α) → Set
ReducesTo {α = α} sig v w = Σ0[ r ∈ Rezz _ α ] ∃[ f ∈ Fuel ] reduce r sig v f ≡ Just w

reduceAppView : ∀ sig (s : Term α)
               → ∃[ t ∈ Term α ]                        ReducesTo sig s t
               → ∃[ (t , vs) ∈ Term α × List (Term α) ] ReducesTo sig s (applys t vs)
reduceAppView sig s (v ⟨ p ⟩) =
  (unApps v) ⟨ subst0 (λ t → ReducesTo sig s t) (sym $ unAppsView v) p ⟩

{-# COMPILE AGDA2HS reduceAppView #-}

