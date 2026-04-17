-- This module is modelling the example test/SigmaRecord.agda but in Agda Core

module Agda.Core.TestProjection where

open import Agda.Core.Prelude

open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.TCM.TCM
open import Agda.Core.Rules.Typing
open import Agda.Core.Checkers.TypeCheck
open import Agda.Core.Rules.Unification
open import Agda.Core.Checkers.Unifier

private variable
  x y : Name
  α : Scope Name

datas = mempty ▸ "Bool" ▸ "Nat" ▸ "Vector"
records = mempty ▸ "Σ"

instance
  globals : Globals
  globals = record
    { defScope = mempty ▸ "sigmaRecordElementProjSnd"
    ; dataScope = datas
    ; recScope = records
    ; dataParScope = λ where
      --Vector
      (⟨ name ⟩ (Zero ⟨ proof₁ ⟩)) -> "A" ◂ mempty
      --Nat and Bool
      _ -> mempty
    ; dataIxScope = λ where
      --Vector
      (⟨ name ⟩ (Zero ⟨ proof₁ ⟩)) -> "length" ◂ mempty
      --Nat and Bool
      _ -> mempty
    ; dataConstructors = λ where
      --Vector
      (⟨ name ⟩ (Zero ⟨ proof₁ ⟩)) -> "Nil" ◂ "Cons" ◂ mempty
      --Nat 
      (⟨ name ⟩ (Suc Zero ⟨ proof₁ ⟩)) -> "Zero" ◂ "Suc" ◂ mempty
      -- and Bool
      _ -> "True" ◂ "False" ◂ mempty 
    ; dataFieldScope = λ where 
      -- True
      {d = ⟨ _ ⟩ (Suc (Suc Zero) ⟨ _ ⟩)} (⟨ _ ⟩ (Zero ⟨ _ ⟩)) → mempty
      -- False
      {d = ⟨ _ ⟩ (Suc (Suc Zero) ⟨ _ ⟩)} (⟨ _ ⟩ (Suc (Zero) ⟨ _ ⟩)) → mempty
      -- Zero
      {d = ⟨ _ ⟩ (Suc (Zero) ⟨ _ ⟩)} (⟨ _ ⟩ (Zero ⟨ _ ⟩)) → mempty
      -- Suc
      {d = ⟨ _ ⟩ (Suc (Zero) ⟨ _ ⟩)} (⟨ _ ⟩ (Suc (Zero) ⟨ _ ⟩)) → "base" ◂ mempty
      -- Nil
      {d = ⟨ _ ⟩ (Zero ⟨ _ ⟩)} (⟨ _ ⟩ (Zero ⟨ _ ⟩)) → mempty
      -- Cons
      _ → "n" ◂ "el" ◂ "vecSmaller" ◂ mempty
    ; recParScope = λ where 
      -- Σ
      _ → "a" ◂ "b" ◂ mempty
    ; recFieldScope = λ where 
      -- Σ
      _ → "fst" ◂ "snd" ◂ mempty
    ; recCon = λ where 
      -- Σ
      _ → {!!}
    }
open module @0 G = Globals globals



nameBool : NameData
nameBool = ⟨ "Bool" ⟩ (Suc (Suc Zero) ⟨ IsSuc (IsSuc (IsZero refl)) ⟩)

nameNat : NameData
nameNat = ⟨ "Nat" ⟩ (Suc Zero ⟨ IsSuc (IsZero refl) ⟩)

nameVector : NameData
nameVector = ⟨ "Vector" ⟩ (Zero ⟨ IsZero refl ⟩)

instance
  {-# TERMINATING #-}
  fuel : Fuel
  fuel = More {{fuel}}

nameTrue : NameDataCon nameBool
nameTrue = ⟨ 'T' ∷ 'r' ∷ 'u' ∷ 'e' ∷ [] ⟩ (Zero ⟨ IsZeroR refl ⟩)

nameFalse : NameDataCon nameBool
nameFalse = ⟨ "False" ⟩ (Suc Zero ⟨ IsSucR (IsZeroR refl) ⟩)

nameZero : NameDataCon nameNat
nameZero = ⟨ "Zero" ⟩ (Zero ⟨ IsZeroR refl ⟩)

nameSuc : NameDataCon nameNat
nameSuc = ⟨ "Suc" ⟩ (Suc Zero ⟨ IsSucR (IsZeroR refl) ⟩)

nameNil : NameDataCon nameVector
nameNil = ⟨ "Nil" ⟩ (Zero ⟨ IsZeroR refl ⟩)

nameCons : NameDataCon nameVector
nameCons = ⟨ "Cons" ⟩ (Suc Zero ⟨ IsSucR (IsZeroR refl) ⟩)


sigDataInstance : (d : NameData) → Datatype d
--Vector
sigDataInstance (⟨ _ ⟩ (Zero ⟨ proof₁ ⟩)) = 
  record { dataSort = STyp 0 
    ; dataParTel = "A" ∶ (El (STyp 1) (TSort (STyp 0))) ◂ EmptyTel -- (A : Set)
    ; dataIxTel = "length" ∶ El (STyp 0) (TData nameNat TSNil TSNil) ◂ EmptyTel -- (length : Nat)
    ; dataConstructors = []}
-- Nat
sigDataInstance (⟨ proj₃ ⟩ (Suc Zero ⟨ proof₁ ⟩)) = Datatype.constructor (STyp 0) EmptyTel EmptyTel []
-- Bool 
sigDataInstance (⟨ proj₃ ⟩ (Suc (Suc value₁) ⟨ proof₁ ⟩)) = Datatype.constructor (STyp 0) EmptyTel EmptyTel []




opaque
  unfolding ScopeThings RScope

  sigConsInstance : (d : NameData) (c : NameDataCon d) → DataConstructor {d = d} c
  -- Vector Nil
  sigConsInstance (⟨ _ ⟩ (Zero ⟨ _ ⟩)) (⟨ _ ⟩ (Zero ⟨ _ ⟩)) = 
    DataConstructor.constructor 
    EmptyTel 
    (TSCons (TDataCon {d = nameNat} nameZero TSNil) TSNil)
  -- Vector Cons
  sigConsInstance (⟨ _ ⟩ (Zero ⟨ _ ⟩)) (⟨ _ ⟩ (Suc _ ⟨ _ ⟩)) = DataConstructor.constructor 
      ("n" ∶ El (STyp 0) (TData nameNat TSNil TSNil) 
      ◂ ("el" ∶ El (STyp 0) (TVar (⟨ "A" ⟩ inThere inHere)) 
      ◂ ("vecSmaller" ∶ 
            El (STyp 0) (TData nameVector 
                          (TSCons (TVar (⟨ "A" ⟩ inThere (inThere inHere))) TSNil) 
                          (TSCons (TVar (⟨ "n" ⟩ inThere inHere)) TSNil)) 
      ◂ EmptyTel))) 
    (TSCons (TDataCon {d = nameNat} nameSuc (TSCons (TVar (⟨ "n" ⟩ inThere (inThere inHere))) TSNil)) TSNil)
  -- Nat Zero
  sigConsInstance (⟨ _ ⟩ (Suc Zero ⟨ _ ⟩)) (⟨ _ ⟩ (Zero ⟨ _ ⟩)) = DataConstructor.constructor 
    EmptyTel
    TSNil
  -- Nat Suc
  sigConsInstance (⟨ _ ⟩ (Suc Zero ⟨ _ ⟩)) (⟨ _ ⟩ (Suc _ ⟨ _ ⟩)) = DataConstructor.constructor 
    {!!}
    TSNil
  -- Bool True
  sigConsInstance (⟨ _ ⟩ (Suc (Suc _) ⟨ _ ⟩)) (⟨ _ ⟩ (Zero ⟨ _ ⟩)) = DataConstructor.constructor 
    {!!}
    TSNil
  -- Bool False
  sigConsInstance (⟨ _ ⟩ (Suc (Suc _) ⟨ _ ⟩)) (⟨ _ ⟩ (Suc _ ⟨ _ ⟩)) = DataConstructor.constructor 
    {!!} 
    TSNil




-- boolsigcons : {@0 d : NameData} (c : NameDataCon d) → DataConstructor {d = d} c
-- boolsigcons _  = record { conIndTel = EmptyTel; conIx = TSNil }


instance
  sig : Signature
  sig .sigData = sigDataInstance
  sig .sigDefs n = {!!}
  sig .sigRecs rn = {!!}
  sig .sigCons d c = sigConsInstance d c




module TestTypechecker (@0 x y z : Name) where

  opaque

    testTerm₁ : Term α
    testTerm₁ = TLam x (TVar (⟨ x ⟩ inHere))
