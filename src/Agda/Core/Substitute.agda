open import Scope

open import Haskell.Prelude hiding (All; coerce; a; b; c; d; t)
open import Haskell.Extra.Dec
open import Haskell.Law.Equality using (subst0; sym; trans)
open import Haskell.Law.Monoid.Def using (leftIdentity; rightIdentity)
open import Haskell.Law.Semigroup.Def using (associativity)
open import Haskell.Extra.Erase

open import Utils.Either

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Syntax

module Agda.Core.Substitute
  {{@0 globals : Globals}}
  where
private open module @0 G = Globals globals

private variable
  @0 x      : Name
  @0 α β γ  : Scope Name
  @0 rγ     : RScope Name
  @0 d      : NameData
  @0 c      : NameCon d
  @0 cs     : RScope (NameCon d)
  t        : @0 Scope Name → Set

data Subst : (@0 α β : Scope Name) → Set where
  SNil  : Subst mempty β
  SCons :  Subst α β → Term β → Subst (α ▸ x) β

{-# COMPILE AGDA2HS Subst deriving Show #-}
infix 4 Subst
syntax Subst α β = α ⇒ β

pattern ⌈⌉ = SNil
infix 6 _▹_↦_
pattern _▹_↦_ σ x u = SCons {x = x} σ u
infix 4 ▹_↦_
pattern ▹_↦_ x u = SCons {x = x} SNil u

rezzSubst : α ⇒ β → Rezz α
rezzSubst ⌈⌉ = rezz mempty
rezzSubst (σ ▹ x ↦ u) = rezzBind (rezzSubst σ)

weakenSubst : α ⊆ β → γ ⇒ α → γ ⇒ β
weakenSubst p ⌈⌉ = ⌈⌉
weakenSubst p (s ▹ x ↦ t) = weakenSubst p s ▹ x ↦ weaken p t
{-# COMPILE AGDA2HS weakenSubst #-}

instance
  iWeakenSubst : Weaken (Subst γ)
  iWeakenSubst .weaken = weakenSubst
  {-# COMPILE AGDA2HS iWeakenSubst #-}

lookupSubst : α ⇒ β
            → (@0 x : Name)
            → x ∈ α
            → Term β
lookupSubst ⌈⌉ x q = inEmptyCase q
lookupSubst (f ▹ _ ↦ u) x q = inBindCase q (lookupSubst f x) (λ _ → u)

{-# COMPILE AGDA2HS lookupSubst #-}

concatSubst : α ⇒ γ → β ⇒ γ → (α <> β) ⇒ γ
concatSubst p ⌈⌉ =
  subst0 (λ α → α ⇒ _) (sym (rightIdentity _)) p
concatSubst p (q ▹ _ ↦ v) =
  subst0 (λ α → α ⇒ _) (sym (associativity _ _ _)) (concatSubst p q ▹ _ ↦ v)

{-# COMPILE AGDA2HS concatSubst #-}

opaque
  unfolding Scope Sub

  subToSubst : Rezz α → α ⊆ β → α ⇒ β
  subToSubst (rezz []) p = ⌈⌉
  subToSubst (rezz (Erased x ∷ α)) p =
    (subToSubst (rezz α) (joinSubLeft (rezz _) p)) ▹ x ↦ (TVar (⟨ x ⟩ coerce p inHere))

{-# COMPILE AGDA2HS subToSubst #-}

extSubst : β ⇒ α → TermS α rγ → (extScope β rγ) ⇒ α
extSubst {α = α} s ⌈⌉ = subst0 (λ γ → γ ⇒ α) (sym extScopeEmpty) s
extSubst {α = α} s (x ↦ u ◂ t) = subst0 (λ γ → γ ⇒ α) (sym extScopeBind) (extSubst (s ▹ x ↦ u) t)
{-# COMPILE AGDA2HS extSubst #-}

liftSubst : {@0 α β γ : Scope Name} → Rezz γ → α ⇒ β → (α <> γ) ⇒ (β <> γ)
liftSubst r f =
  concatSubst (weaken (subJoinDrop r subRefl) f)
              (subToSubst r (subJoinHere r subRefl))
{-# COMPILE AGDA2HS liftSubst #-}

idSubst : {@0 β : Scope Name} → Rezz β → β ⇒ β
idSubst r = subst0 (λ β → β ⇒ β) (leftIdentity _) (liftSubst r ⌈⌉)
{-# COMPILE AGDA2HS idSubst #-}

liftBindSubst : {@0 α β : Scope Name} {@0 x y : Name} → α ⇒ β → α ▸ x ⇒ β ▸ y
liftBindSubst {y = y} e = (weaken (subBindDrop subRefl) e) ▹ _ ↦ (TVar (⟨ y ⟩ inHere))
{-# COMPILE AGDA2HS liftBindSubst #-}

opaque
  unfolding extScope -- if we had an induction principle for RScope we could avoid the unfolding
  substExtScope : (Rezz rγ) → α ⇒ β → α ⇒ (extScope β rγ)
  substExtScope (rezz []) s = s
  substExtScope (rezz (x ∷ rγ)) s = substExtScope (rezz rγ) (weaken (subBindDrop subRefl) s)
  {-# COMPILE AGDA2HS substExtScope #-}


  substExtScopeKeep : (Rezz rγ) → α ⇒ β → (extScope α rγ) ⇒ (extScope β rγ)
  substExtScopeKeep (rezz []) p = p
  substExtScopeKeep (rezz (x ∷ rγ)) p = substExtScopeKeep (rezz rγ) (liftBindSubst p)
  {-# COMPILE AGDA2HS substExtScopeKeep #-}


substTerm     : α ⇒ β → Term α → Term β
substSort     : α ⇒ β → Sort α → Sort β
substType     : α ⇒ β → Type α → Type β
substBranch   : α ⇒ β → Branch α {d = d} c → Branch β c
substBranches : α ⇒ β → Branches α d cs → Branches β d cs
substTermS   : α ⇒ β → TermS α rγ → TermS β rγ

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
    (substType (liftBindSubst (substExtScopeKeep r f)) m)
substTerm f (TPi x a b)       = TPi x (substType f a) (substType (liftBindSubst f) b)
substTerm f (TSort s)         = TSort (substSort f s)
substTerm f (TLet x u v)      = TLet x (substTerm f u) (substTerm (liftBindSubst f) v)
substTerm f (TAnn u t)        = TAnn (substTerm f u) (substType f t)
{-# COMPILE AGDA2HS substTerm #-}

substBranch f (BBranch rc r u) = BBranch rc r (substTerm (substExtScopeKeep r f) u)
{-# COMPILE AGDA2HS substBranch #-}

substBranches f BsNil = BsNil
substBranches f (BsCons b bs) = BsCons (substBranch f b) (substBranches f bs)
{-# COMPILE AGDA2HS substBranches #-}

substTermS f ⌈⌉ = ⌈⌉
substTermS f (_ ↦ x ◂ e) = TSCons (substTerm f x) (substTermS f e)
{-# COMPILE AGDA2HS substTermS #-}

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
  iSubstBranch : Substitute (λ α → Branch α {d = d} c)
  iSubstBranch .subst = substBranch
  iSubstBranches : Substitute (λ α → Branches α d cs)
  iSubstBranches .subst = substBranches
  iSubstTermS : Substitute (λ α → TermS α rγ)
  iSubstTermS .subst = substTermS
{-# COMPILE AGDA2HS iSubstTerm #-}
{-# COMPILE AGDA2HS iSubstType #-}
{-# COMPILE AGDA2HS iSubstSort #-}
{-# COMPILE AGDA2HS iSubstBranch #-}
{-# COMPILE AGDA2HS iSubstBranches #-}
{-# COMPILE AGDA2HS iSubstTermS #-}

substTop : {{Substitute t}} → Rezz α → Term α → t (α ▸ x) → t α
substTop r u = subst (idSubst r ▹ _ ↦ u)
{-# COMPILE AGDA2HS substTop #-}

substTelescope : (α ⇒ β) → Telescope α rγ → Telescope β rγ
substTelescope f EmptyTel = EmptyTel
substTelescope f (ExtendTel x a tel) = ExtendTel x (substType f a) (substTelescope (liftBindSubst f) tel)
{-# COMPILE AGDA2HS substTelescope #-}

instance
  iSubstTelescope : Substitute (λ α → Telescope α rγ)
  iSubstTelescope .subst = substTelescope
{-# COMPILE AGDA2HS iSubstTelescope #-}

composeSubst : α ⇒ β → β ⇒ γ → α ⇒ γ
composeSubst ⌈⌉ _ = ⌈⌉
composeSubst (s1 ▹ x ↦ u) s2 = composeSubst s1 s2 ▹ x ↦ subst s2 u
{-# COMPILE AGDA2HS composeSubst #-}
