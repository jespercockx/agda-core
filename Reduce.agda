{-# OPTIONS --allow-unsolved-metas #-}

open import Utils
open import Scope

module Reduce 
    {Name : Set} 
    (iScope : IScope Name) (let open IScope iScope) 
    (defs : Scope)
    (cons     : Scope)
    (conArity : All (λ _ → Scope) cons) 
  where

open import Syntax iScope defs cons conArity

{-# TERMINATING #-}
substTerm  : α ⇒ β → Term α → Term β
substSort  : α ⇒ β → Sort α → Sort β
substElim  : α ⇒ β → Elim α → Elim β
substElims : α ⇒ β → Elims α → Elims β
substBranch : α ⇒ β → Branch α → Branch β
substBranches : α ⇒ β → Branches α → Branches β
substEnv : α ⇒ β → γ ⇒ α → γ ⇒ β

substTerm f (var x)           = lookupEnv f x
substTerm f (def d)           = def d
substTerm f (con c vs)        = con c (substEnv f vs)
substTerm f (lam x v)         = lam x (substTerm (liftEnv f) v)
substTerm f (appE u es)       = appE (substTerm f u) (substElims f es)
substTerm f (pi x a b)        = pi x (substTerm f a) (substTerm (liftEnv f) b)
substTerm f (sort s)          = sort (substSort f s)
substTerm f (let′ x u v)      = let′ x (substTerm f u) (substTerm (liftEnv f) v)
substTerm f (case x {{p}} bs) = 
  let′ x (lookupEnv f x) 
      (case x {{here}} (substBranches (coerceEnv (diff-⊆ p) f) bs))

substSort f (type x) = type x

substElim f (arg u) = arg (substTerm f u)
substElim f (proj p) = proj p

substElims f [] = []
substElims f (e ∷ es) = substElim f e ∷ substElims f es

substBranch f (branch c u) = branch c (substTerm (liftEnv f) u)

substBranches f [] = []
substBranches f (b ∷ bs) = substBranch f b ∷ substBranches f bs

substEnv f (⇒weaken x) = coerceEnv x f
substEnv f (⇒const x) = ⇒const (substTerm f x)
substEnv f (⇒join x g₁ g₂) = ⇒join x (substEnv f g₁) (substEnv f g₂)

substTop : Term α → Term (x ◃ α) → Term α
substTop {α = α} u = substTerm (⇒join ⋈-refl (⇒const u) (⇒weaken ⊆-refl))

lookupBranch : Branches α → (@0 c : Name) {{p : c ∈ cons}} → Maybe (Term ((conArity ! c) <> α))
lookupBranch [] c = nothing
lookupBranch (branch c₁ {{p}} v ∷ bs) c {{q}} = case c ≟ c₁ of λ where
  (yes refl) → just v
  (no _)     → lookupBranch bs c

step : {α : Scope} → Term α → Maybe (Term α)
step (var x) = nothing
step (def x) = nothing
step (con c vs) = nothing
step (lam x u) = nothing
step (appE u []) = just u
step (appE (lam x u) (arg v ∷ es)) = just (substTop v u)
step (appE u es) = Maybe.map (λ u → appE u es) (step u)
step (pi x a b) = nothing
step (sort x) = nothing
step (let′ x (con c us) (case y {{p}} bs)) = 
  case p ∈-≟ here of λ where
    (yes refl) → case lookupBranch bs c of λ where
      (just v) → just (substTerm (raiseEnv us) v)
      nothing → nothing
    (no _) → nothing
step (let′ x u v) = case step u of λ where
  (just u') → just (let′ x u' v)
  nothing   → just (substTop u v)
step (case x bs) = nothing

reduce : {α : Scope} → ℕ → Term α → Maybe (Term α)
reduce zero u = nothing
reduce (suc n) u = case (step u) of λ where
  (just u') → reduce n u'
  nothing   → just u
