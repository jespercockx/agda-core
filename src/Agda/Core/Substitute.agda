open import Scope

open import Haskell.Prelude hiding (All; coerce; a; b; c; t)
open import Haskell.Extra.Dec
open import Haskell.Law.Equality using (subst0; sym; trans)
open import Haskell.Law.Monoid.Def using (leftIdentity; rightIdentity)
open import Haskell.Law.Semigroup.Def using (associativity)
open import Haskell.Extra.Erase

open import Utils.Either

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Syntax
open import Agda.Core.Signature

module Agda.Core.Substitute
  {{@0 globals : Globals}}
  where

private variable
  @0 x c     : Name
  @0 α β γ cs : Scope Name
  @0 rγ : RScope Name
  t : @0 Scope Name → Set

data Subst : (@0 α β : Scope Name) → Set where
  SNil  : Subst mempty β
  SCons :  Term β → Subst α β → Subst (x ◃ α) β

{-# COMPILE AGDA2HS Subst deriving Show #-}
infix 5 Subst
syntax Subst α β = α ⇒ β

pattern ⌈⌉ = SNil
infix 6 ⌈_◃_↦_⌉
pattern ⌈_◃_↦_⌉ σ x u = SCons {x = x} u σ
infix 4 ⌈◃_↦_⌉
pattern ⌈◃_↦_⌉ x u = ⌈ ⌈⌉ ◃ x ↦ u ⌉

rezzSubst : α ⇒ β → Rezz α
rezzSubst ⌈⌉ = rezz mempty
rezzSubst ⌈ σ ◃ x ↦ u ⌉ = rezzBind (rezzSubst σ)

weakenSubst : α ⊆ β → γ ⇒ α → γ ⇒ β
weakenSubst p ⌈⌉ = ⌈⌉
weakenSubst p ⌈ s ◃ x ↦ t ⌉ = ⌈ weakenSubst p s ◃ x ↦ weaken p t ⌉

instance
  iWeakenSubst : Weaken (Subst γ)
  iWeakenSubst .weaken = weakenSubst
  {-# COMPILE AGDA2HS iWeakenSubst #-}

lookupSubst : α ⇒ β
            → (@0 x : Name)
            → x ∈ α
            → Term β
lookupSubst ⌈⌉ x q = inEmptyCase q
lookupSubst ⌈ f ◃ _ ↦ u ⌉ x q = inBindCase q (λ _ → u) (lookupSubst f x)

{-# COMPILE AGDA2HS lookupSubst #-}

concatSubst : α ⇒ γ → β ⇒ γ → (α <> β) ⇒ γ
concatSubst ⌈⌉ q =
  subst0 (λ α → α ⇒ _) (sym (leftIdentity _)) q
concatSubst ⌈ p ◃ _ ↦ v ⌉ q =
  subst0 (λ α → α ⇒ _) (associativity _ _ _) ⌈ concatSubst p q ◃ _ ↦ v ⌉

{-# COMPILE AGDA2HS concatSubst #-}

opaque
  unfolding Scope Sub

  subToSubst : Rezz α → α ⊆ β → α ⇒ β
  subToSubst (rezz []) p = ⌈⌉
  subToSubst (rezz (Erased x ∷ α)) p =
    ⌈ (subToSubst (rezz α) (joinSubRight (rezz _) p)) ◃ x ↦ (TVar (⟨ x ⟩ coerce p inHere)) ⌉

{-# COMPILE AGDA2HS subToSubst #-}


opaque
  unfolding Scope revScope

  revSubstAcc : {@0 α β γ : Scope Name} → α ⇒ γ → β ⇒ γ → (revScopeAcc α β) ⇒ γ
  revSubstAcc ⌈⌉ p = p
  revSubstAcc ⌈ s ◃ y ↦ x ⌉ p = revSubstAcc s ⌈ p ◃ y ↦ x ⌉
  {-# COMPILE AGDA2HS revSubstAcc #-}

  revSubst : {@0 α β : Scope Name} → α ⇒ β → ~ α ⇒ β
  revSubst = flip revSubstAcc ⌈⌉
  {-# COMPILE AGDA2HS revSubst #-}

liftSubst : {@0 α β γ : Scope Name} → Rezz α → β ⇒ γ → (α <> β) ⇒ (α <> γ)
liftSubst r f =
  concatSubst (subToSubst r (subJoinHere r subRefl))
              (weaken (subJoinDrop r subRefl) f)
{-# COMPILE AGDA2HS liftSubst #-}

{-# COMPILE AGDA2HS liftSubst #-}
idSubst : {@0 β : Scope Name} → Rezz β → β ⇒ β
idSubst r = subst0 (λ β → β ⇒ β) (rightIdentity _) (liftSubst r ⌈⌉)
{-# COMPILE AGDA2HS idSubst #-}

liftBindSubst : {@0 α β : Scope Name} {@0 x y : Name} → α ⇒ β → (bind x α) ⇒ (bind y β)
liftBindSubst {y = y} e = ⌈ (weaken (subBindDrop subRefl) e) ◃ _ ↦ (TVar (⟨ y ⟩ inHere)) ⌉
{-# COMPILE AGDA2HS liftBindSubst #-}

raiseSubst : {@0 α β : Scope Name} → Rezz β → α ⇒ β → (α <> β) ⇒ β
raiseSubst {β = β} r ⌈⌉ = subst0 (λ α → α ⇒ β) (sym (leftIdentity β)) (idSubst r)
raiseSubst {β = β} r (SCons {α = α} u e) =
  subst0 (λ α → α ⇒ β)
    (associativity (singleton _) α β)
    ⌈ raiseSubst r e ◃ _ ↦ u ⌉
{-# COMPILE AGDA2HS raiseSubst #-}

revIdSubst : {@0 α : Scope Name} → Rezz α → α ⇒ ~ α
revIdSubst {α} r = subst0 (λ s →  s ⇒ (~ α)) (revsInvolution α) (revSubst (idSubst (rezz~ r)))
{-# COMPILE AGDA2HS revIdSubst #-}

revIdSubst' : {@0 α : Scope Name} → Rezz α → ~ α ⇒ α
revIdSubst' {α} r = subst0 (λ s →  (~ α) ⇒ s) (revsInvolution α) (revIdSubst (rezz~ r))
{-# COMPILE AGDA2HS revIdSubst' #-}

substExtScope : α ⇒ β → (Rezz rγ) → (extScope α rγ) ⇒ (extScope β rγ)
substExtScope p (rezz Nil) = p
substExtScope p (rezz (x ◂ rγ)) = substExtScope (liftBindSubst p) (rezz rγ)

substTerm     : α ⇒ β → Term α → Term β
substSort     : α ⇒ β → Sort α → Sort β
substType     : α ⇒ β → Type α → Type β
substBranch   : α ⇒ β → Branch α c → Branch β c
substBranches : α ⇒ β → Branches α cs → Branches β cs
substTermS   : α ⇒ β → TermS α rγ → TermS β rγ
substTypeS   : α ⇒ β → TypeS α rγ → TypeS β rγ

substSort f (STyp x) = STyp x
{-# COMPILE AGDA2HS substSort #-}

substType f (El st t) = El (substSort f st) (substTerm f t)
{-# COMPILE AGDA2HS substType #-}

substTerm f (TVar (⟨ x ⟩ k))  = lookupSubst f x k
substTerm f (TDef d)          = TDef d
substTerm f (TData d ps is)   = TData d (substTermS f ps) (substTermS f is)
substTerm f (TCon c vs)       = TCon c (substTermS f vs)
substTerm f (TLam x v)        = TLam x (substTerm (liftBindSubst f) v)
substTerm f (TApp u v)        = TApp (substTerm f u) (substTerm f v)
substTerm f (TProj u p)       = TProj (substTerm f u) p
substTerm f (TCase {x = x} d r u bs m) =
  TCase {x = x} d r
    (substTerm f u)
    (substBranches f bs)
    (substType (liftBindSubst (substExtScope f r)) m)
substTerm f (TPi x a b)       = TPi x (substType f a) (substType (liftBindSubst f) b)
substTerm f (TSort s)         = TSort (substSort f s)
substTerm f (TLet x u v)      = TLet x (substTerm f u) (substTerm (liftBindSubst f) v)
substTerm f (TAnn u t)        = TAnn (substTerm f u) (substType f t)
{-# COMPILE AGDA2HS substTerm #-}

substBranch f (BBranch c r u) = BBranch c r (substTerm (substExtScope f r) u)
{-# COMPILE AGDA2HS substBranch #-}

substBranches f BsNil = BsNil
substBranches f (BsCons b bs) = BsCons (substBranch f b) (substBranches f bs)
{-# COMPILE AGDA2HS substBranches #-}

substTermS f ⌈⌉ = ⌈⌉
substTermS f (_ ↦ x ◂ e) = TSCons (substTerm f x) (substTermS f e)
{-# COMPILE AGDA2HS substTermS #-}

substTypeS f ⌈⌉ = ⌈⌉
substTypeS {rγ = x ◂ rγ} f (_ ∶ u ◂ e) = YCons (substType (substExtScope {rγ = rγ} f (rezzTypeS e)) u) (substTypeS f e)
{-# COMPILE AGDA2HS substTypeS #-}

record Substitute (t : @0 Scope Name → Set) : Set where
  field subst : (α ⇒ β) → t α → t β
open Substitute {{...}} public
{-# COMPILE AGDA2HS Substitute class #-}

instance
  iSubstTerm : Substitute Term
  iSubstTerm .subst = substTerm
  iSubstType : Substitute Type
  iSubstType .subst = substType
  iSubstSort : Substitute Sort
  iSubstSort .subst = substSort
  iSubstBranch : Substitute (λ α → Branch α c)
  iSubstBranch .subst = substBranch
  iSubstBranches : Substitute (λ α → Branches α cs)
  iSubstBranches .subst = substBranches
  iSubstTermS : Substitute (λ α → TermS α rγ)
  iSubstTermS .subst = substTermS
  iSubstTypeS : Substitute (λ α → TypeS α rγ)
  iSubstTypeS .subst = substTypeS
{-# COMPILE AGDA2HS iSubstTerm #-}
{-# COMPILE AGDA2HS iSubstType #-}
{-# COMPILE AGDA2HS iSubstSort #-}
{-# COMPILE AGDA2HS iSubstBranch #-}
{-# COMPILE AGDA2HS iSubstBranches #-}
{-# COMPILE AGDA2HS iSubstTermS #-}
{-# COMPILE AGDA2HS iSubstTypeS #-}

substTop : {{Substitute t}} → Rezz α → Term α → t (x ◃ α) → t α
substTop r u = subst (SCons u (idSubst r))
{-# COMPILE AGDA2HS substTop #-}

substTelescope : (α ⇒ β) → Telescope α γ → Telescope β γ
substTelescope f EmptyTel = EmptyTel
substTelescope f (ExtendTel x a tel) = ExtendTel x (substType f a) (substTelescope (liftBindSubst f) tel)
{-# COMPILE AGDA2HS substTelescope #-}

instance
  iSubstTelescope : Substitute (λ α → Telescope α β)
  iSubstTelescope .subst = substTelescope
{-# COMPILE AGDA2HS iSubstTelescope #-}
