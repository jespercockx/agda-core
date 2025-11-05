open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax.Term
open import Agda.Core.Syntax.Context

module Agda.Core.Syntax.Weakening
  {{@0 globals : Globals}}
  where

private open module @0 G = Globals globals

private variable
  @0 α β : Scope Name
  @0 rγ  : RScope Name
  @0 d   : NameData
  @0 c   : NameCon d
  @0 cs  : RScope (NameCon d)

weakenTerm     : α ⊆ β → Term α → Term β
weakenTermS    : α ⊆ β → TermS α rγ → TermS β rγ
weakenSort     : α ⊆ β → Sort α → Sort β
weakenType     : α ⊆ β → Type α → Type β
weakenBranch   : α ⊆ β → Branch α {d = d} c → Branch β {d = d} c
weakenBranches : α ⊆ β → Branches α d cs → Branches β d cs

weakenTerm p (TVar (⟨ x ⟩ k))  = TVar (⟨ x ⟩ coerce p k)
weakenTerm p (TDef d)          = TDef d
weakenTerm p (TData d ps is)   = TData d (weakenTermS p ps) (weakenTermS p is)
weakenTerm p (TCon c vs)       = TCon c (weakenTermS p vs)
weakenTerm p (TLam x v)        = TLam x (weakenTerm (subBindKeep p) v)
weakenTerm p (TApp u e)        = TApp (weakenTerm p u) (weakenTerm p e)
weakenTerm p (TProj u x)       = TProj (weakenTerm p u) x
weakenTerm p (TCase d r u bs m) = TCase d r (weakenTerm p u) (weakenBranches p bs) (weakenType (subBindKeep (subExtScopeKeep r p)) m)
weakenTerm p (TPi x a b)       = TPi x (weakenType p a) (weakenType (subBindKeep p) b)
weakenTerm p (TSort α)         = TSort (weakenSort p α)
weakenTerm p (TLet x v t)      = TLet x (weakenTerm p v) (weakenTerm (subBindKeep p) t)
weakenTerm p (TAnn u t)        = TAnn (weakenTerm p u) (weakenType p t)

weakenTermS p ⌈⌉ = ⌈⌉
weakenTermS p (_ ↦ u ◂ e) = TSCons (weakenTerm p u) (weakenTermS p e)

weakenType p (El st t) = El (weakenSort p st) (weakenTerm p t)

weakenSort p (STyp x) = STyp x

weakenBranch p (BBranch rc r x) = BBranch rc r (weakenTerm (subExtScopeKeep r p) x)

weakenBranches p BsNil         = BsNil
weakenBranches p (BsCons b bs) = BsCons (weakenBranch p b) (weakenBranches p bs)

{-# COMPILE AGDA2HS weakenBranches #-}
{-# COMPILE AGDA2HS weakenTerm #-}
{-# COMPILE AGDA2HS weakenTermS #-}
{-# COMPILE AGDA2HS weakenType #-}
{-# COMPILE AGDA2HS weakenSort #-}
{-# COMPILE AGDA2HS weakenBranch #-}

record Weaken (t : @0 Scope Name → Set) : Set where
  field
    weaken : α ⊆ β → t α → t β
open Weaken {{...}} public
{-# COMPILE AGDA2HS Weaken class #-}

instance
  iWeakenTerm : Weaken Term
  iWeakenTerm .weaken = weakenTerm
  iWeakenTermS : Weaken (λ α → TermS α rγ)
  iWeakenTermS .weaken = weakenTermS
  iWeakenSort : Weaken Sort
  iWeakenSort .weaken = weakenSort
  iWeakenType : Weaken Type
  iWeakenType .weaken = weakenType
  iWeakenBranch : Weaken (λ α → Branch α {d = d} c)
  iWeakenBranch .weaken = weakenBranch
  iWeakenBranches : Weaken (λ α → Branches α d cs)
  iWeakenBranches .weaken = weakenBranches
{-# COMPILE AGDA2HS iWeakenTerm #-}
{-# COMPILE AGDA2HS iWeakenTermS #-}
{-# COMPILE AGDA2HS iWeakenSort #-}
{-# COMPILE AGDA2HS iWeakenType #-}
{-# COMPILE AGDA2HS iWeakenBranch #-}
{-# COMPILE AGDA2HS iWeakenBranches #-}

weakenTel : α ⊆ β → Telescope α rγ → Telescope β rγ
weakenTel p ⌈⌉ = ⌈⌉
weakenTel p (x ∶ ty ◂ t) = x ∶ (weaken p ty) ◂ (weakenTel (subBindKeep p) t)
{-# COMPILE AGDA2HS weakenTel #-}

instance
  iWeakenTel : Weaken (λ α → Telescope α rγ)
  iWeakenTel .weaken = weakenTel
{-# COMPILE AGDA2HS iWeakenTel #-}

---------------------------------------------------------------------------------------------------
                                      {- Useful functions -}
---------------------------------------------------------------------------------------------------

raise : Rezz rγ → Term α → Term (α ◂▸ rγ)
raise r = weakenTerm (subExtScope r subRefl)
{-# COMPILE AGDA2HS raise #-}

private -- it should use a RScope instead of β and then could be public
  raiseType : {@0 α β : Scope Name} → Rezz β → Type α → Type (α <> β)
  raiseType r = weakenType (subJoinDrop r subRefl)
  {-# COMPILE AGDA2HS raiseType #-}

lookupVar : (Γ : Context α) (x : NameIn α) → Type α
lookupVar CtxEmpty x = nameInEmptyCase x
lookupVar (CtxExtend g y s) x = raiseType (rezz _) (nameInBindCase x
  (λ q → lookupVar g (⟨ _ ⟩ q))
  (λ _ → s))
{-# COMPILE AGDA2HS lookupVar #-}
