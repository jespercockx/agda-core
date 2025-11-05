
open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax

-- TODO: Split in two files: rules and checkers

module Agda.Core.Reduce
  {{@0 globals : Globals}}
  {{@0 sig : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x      : Name
  @0 α β γ  : Scope Name
  @0 rγ     : RScope Name
  @0 u v w  : Term α
  @0 d      : NameData

data Environment : (@0 α β : Scope Name) → Set where
  EnvNil  : Environment α α
  EnvCons : Environment α β → (@0 x : Name) → Term β → Environment α  (β ▸ x)

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

envToSubst : Rezz α → Environment α β → β ⇒ α
envToSubst r EnvNil = idSubst r
envToSubst r (env , x ↦ v) =
  let s = envToSubst r env
  in  s ▹ x ↦ (subst s v)

{-# COMPILE AGDA2HS envToSubst #-}

data Frame (@0 α : Scope Name) : Set where
  FApp  : (u : Term α) → Frame α
  FProj : (x : NameIn defScope) → Frame α
  FCase : (d : NameData) (r : Rezz (dataIxScope d))
          (bs : Branches α d (AllNameCon d)) (m : Type (α ◂▸ dataIxScope d ▸ x)) → Frame α

{-# COMPILE AGDA2HS Frame #-}

unFrame : Frame α → Term α → Term α
unFrame (FApp v) u = TApp u v
unFrame (FProj f) u = TProj u f
unFrame (FCase d r bs m) u = TCase d r u bs m

{-# COMPILE AGDA2HS unFrame #-}

weakenFrame : α ⊆ β → Frame α → Frame β
weakenFrame s (FApp u) = FApp (weaken s u)
weakenFrame s (FProj f) = FProj f
weakenFrame s (FCase d r bs m) =
  FCase d r
    (weaken s bs)
    (weaken (subBindKeep (subExtScopeKeep r s)) m)

{-# COMPILE AGDA2HS weakenFrame #-}

Stack : (@0 α : Scope Name) → Set
Stack α = List (Frame α)

{-# COMPILE AGDA2HS Stack #-}

unStack : Stack α → Term α → Term α
unStack [] u = u
unStack (f ∷ fs) u = unStack fs (unFrame f u)

{-# COMPILE AGDA2HS unStack #-}

weakenStack : α ⊆ β → Stack α → Stack β
weakenStack s [] = []
weakenStack s (f ∷ fs) = weakenFrame s f ∷ weakenStack s fs

{-# COMPILE AGDA2HS weakenStack #-}

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

unState : Rezz α → State α → Term α
unState r (MkState e v s) = subst (envToSubst r e) (unStack s v)

{-# COMPILE AGDA2HS unState #-}

lookupBranch : {@0 cs : RScope (NameCon d)} → Branches α d cs → (c : NameCon d)
             → Maybe ( Rezz (fieldScope c)
                     × Term (α ◂▸ fieldScope c))
lookupBranch BsNil c = Nothing
lookupBranch {d = d} (BsCons (BBranch (rezz c') aty u) bs) c =
    case decNamesInR c' c of λ where
      (True  ⟨ refl ⟩) →  Just (aty , u)
      (False ⟨ _    ⟩) → lookupBranch bs c

{-# COMPILE AGDA2HS lookupBranch #-}

opaque
  unfolding extScope
  extendEnvironment : TermS β rγ → Environment α β → Environment α (β ◂▸ rγ)
  extendEnvironment vs e = aux (rezzTermS vs) vs e
    where
      aux : Rezz rγ → TermS β rγ → Environment α β → Environment α (β ◂▸ rγ)
      aux r ⌈⌉ e = e
      aux (rezz (Erased x ∷ rγ₀)) (TSCons {rβ = rγ₀} {x = x} v vs) e =
        aux (rezz rγ₀) (weaken (subBindDrop subRefl) vs) (e , x ↦ v)
  {-# COMPILE AGDA2HS extendEnvironment #-}

lookupEnvironment : Environment α β → x ∈ β → Either (x ∈ α) (Term β)
lookupEnvironment EnvNil      p = Left p
lookupEnvironment (e , x ↦ v) p = inBindCase p
  (λ p → mapRight (weaken (subBindDrop subRefl)) (lookupEnvironment e p))
  (λ _ → Right (weaken (subBindDrop subRefl) v))
{-# COMPILE AGDA2HS lookupEnvironment #-}

step : (rsig : Rezz sig) (s : State α) → Maybe (State α)
step rsig (MkState e (TVar (⟨ x ⟩ p)) s) =
  case lookupEnvironment e p of λ where
    (Left _) → Nothing
    (Right v) → Just (MkState e v s)
step rsig (MkState e (TApp v w) s) = Just (MkState e v (FApp w ∷ s))
step rsig (MkState e (TProj v f) s) = Just (MkState e v (FProj f ∷ s))
step rsig (MkState e (TCase d r v bs m) s) = Just (MkState e v (FCase d r bs m ∷ s))
step rsig (MkState e (TLam x v) (FApp w ∷ s)) =
  Just (MkState
    (e , x ↦ w)
    v
    (weakenStack (subBindDrop subRefl) s))
step rsig (MkState e (TLet x v w) s) =
  Just (MkState
    (e , x ↦ v)
    w
    (weakenStack (subBindDrop subRefl) s))
step (rezz sig) (MkState e (TDef d) s) =
  case getBody sig d of λ where
    v → Just (MkState e (weaken subEmpty v) s)
step rsig (MkState e (TCon {d = d'} c vs) (FCase d r bs _ ∷ s)) =
  case decNamesIn d' d of λ where
      (True  ⟨ refl ⟩) → case lookupBranch bs c of λ where
        (Just (r , v)) → Just (MkState
          (extendEnvironment vs e)
          v
          (weakenStack (subExtScope r subRefl) s))
        Nothing  → Nothing
      (False  ⟨ _ ⟩) → Nothing
step rsig (MkState e (TData d ps is) s) = Nothing
step rsig (MkState e (TCon c vs) (FProj f ∷ s)) = Nothing -- TODO
step rsig (MkState e (TCon c x) s) = Nothing
step rsig (MkState e (TLam x v) s) = Nothing
step rsig (MkState e (TPi x a b) s) = Nothing
step rsig (MkState e (TSort n) s) = Nothing
step rsig (MkState e (TAnn u t) s) = Just (MkState e u s) -- TODO preserve annotations on non-inferrable terms

{-# COMPILE AGDA2HS step #-}

reduce : Rezz α
       → (rsig : Rezz sig) (v : Term α) → {{Fuel}} → Maybe (Term α)
reduce {α = α} r rsig v = go (makeState v)
  where
    go : (s : State α) → {{Fuel}} → Maybe (Term α)
    go s {{None}}        = Nothing
    go s {{More {{fl}}}} = case (step rsig s) of λ where
          (Just s') → go s' {{fl}}
          Nothing   → Just (unState r s)
{-# COMPILE AGDA2HS reduce #-}

reduceClosed : (rsig : Rezz sig) (v : Term mempty) → {{Fuel}} → Maybe (Term mempty)
reduceClosed = reduce (rezz _)

{-# COMPILE AGDA2HS reduceClosed #-}

ReducesTo : (v w : Term α) → Set
ReducesTo {α = α} v w = Σ0[ r ∈ Rezz α ] Σ0[ rsig ∈ Rezz sig ] ∃[ f ∈ Fuel ] reduce r rsig v {{f}} ≡ Just w

reduceAppView : ∀ (s : Term α)
               → ∃[ t ∈ Term α ]                        ReducesTo s t
               → ∃[ (t , vs) ∈ Term α × List (Term α) ] ReducesTo s (applys t vs)
reduceAppView s (v ⟨ p ⟩) =
  (unApps v) ⟨ subst0 (λ t → ReducesTo s t) (sym $ unAppsView v) p ⟩

{-# COMPILE AGDA2HS reduceAppView #-}
