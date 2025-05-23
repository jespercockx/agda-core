open import Haskell.Prelude hiding (All; coerce; a; b; c; d)

open import Agda.Core.Name
open import Agda.Core.Utils
open import Agda.Core.Syntax.Term

module Agda.Core.Syntax.Strengthening
  {{@0 globals : Globals}}
  where

private open module @0 G = Globals globals

private variable
  @0 α β  : Scope Name
  @0 rγ   : RScope Name
  @0 d    : NameData
  @0 c    : NameCon d
  @0 cs   : RScope (NameCon d)

strengthenTerm      : α ⊆ β → Term β → Maybe (Term α)
strengthenTermS     : α ⊆ β → TermS β rγ → Maybe (TermS α rγ)
strengthenType      : α ⊆ β → Type β → Maybe (Type α)
strengthenSort      : α ⊆ β → Sort β → Maybe (Sort α)
strengthenBranch    : α ⊆ β → Branch β {d = d} c → Maybe (Branch α {d = d} c)
strengthenBranches  : α ⊆ β → Branches β d cs → Maybe (Branches α d cs)

strengthenTerm p (TVar (⟨ x ⟩ q)) = diffCase p q (λ q → Just (TVar (⟨ x ⟩ q))) (λ _ → Nothing)
strengthenTerm p (TDef d) = Just (TDef d)
strengthenTerm p (TData d ps is) = TData d <$> strengthenTermS p ps <*> strengthenTermS p is
strengthenTerm p (TCon c vs) = TCon c <$> strengthenTermS p vs
strengthenTerm p (TLam x v) = TLam x <$> strengthenTerm (subBindKeep p) v
strengthenTerm p (TApp v e) = TApp <$> strengthenTerm p v <*> strengthenTerm p e
strengthenTerm p (TProj u f) = (λ v → TProj v f) <$> strengthenTerm p u
strengthenTerm p (TCase d r u bs m) =
  TCase d r <$> strengthenTerm p u
            <*> strengthenBranches p bs
            <*> strengthenType (subBindKeep (subExtScopeKeep r p)) m
strengthenTerm p (TPi x a b) =
  TPi x <$> strengthenType p a <*> strengthenType (subBindKeep p) b
strengthenTerm p (TSort s) = TSort <$> strengthenSort p s
strengthenTerm p (TLet x u v) = TLet x <$> strengthenTerm p u <*> strengthenTerm (subBindKeep p) v
strengthenTerm p (TAnn u t) = TAnn <$> strengthenTerm p u <*> strengthenType p t

strengthenTermS p ⌈⌉ = Just ⌈⌉
strengthenTermS p (x ↦ v ◂ vs) = TSCons <$> strengthenTerm p v <*> strengthenTermS p vs

strengthenType p (El st t) = El <$> strengthenSort p st <*> strengthenTerm p t

strengthenSort p (STyp n) = Just (STyp n)

strengthenBranch p (BBranch rc r v) = BBranch rc r <$> strengthenTerm (subExtScopeKeep r p) v

strengthenBranches p BsNil = Just BsNil
strengthenBranches p (BsCons b bs) = BsCons <$> strengthenBranch p b <*> strengthenBranches p bs

{-# COMPILE AGDA2HS strengthenTerm #-}
{-# COMPILE AGDA2HS strengthenTermS #-}
{-# COMPILE AGDA2HS strengthenType #-}
{-# COMPILE AGDA2HS strengthenSort #-}
{-# COMPILE AGDA2HS strengthenBranch #-}
{-# COMPILE AGDA2HS strengthenBranches #-}

record Strengthen (t : @0 Scope Name → Set) : Set where
  field
    strengthen : α ⊆ β → t β → Maybe (t α)
open Strengthen {{...}} public
{-# COMPILE AGDA2HS Strengthen class #-}

instance
  iStrengthenTerm : Strengthen Term
  iStrengthenTerm .strengthen = strengthenTerm
  iStrengthenTermS : Strengthen (λ α → TermS α rγ)
  iStrengthenTermS .strengthen = strengthenTermS
  iStrengthenType : Strengthen Type
  iStrengthenType .strengthen = strengthenType
  iStrengthenSort : Strengthen Sort
  iStrengthenSort .strengthen = strengthenSort
  iStrengthenBranch : Strengthen (λ α → Branch α {d = d} c)
  iStrengthenBranch .strengthen = strengthenBranch
  iStrengthenBranches : Strengthen (λ α → Branches α d cs)
  iStrengthenBranches .strengthen = strengthenBranches

{-# COMPILE AGDA2HS iStrengthenTerm #-}
{-# COMPILE AGDA2HS iStrengthenTermS #-}
{-# COMPILE AGDA2HS iStrengthenType #-}
{-# COMPILE AGDA2HS iStrengthenSort #-}
{-# COMPILE AGDA2HS iStrengthenBranch #-}
{-# COMPILE AGDA2HS iStrengthenBranches #-}
