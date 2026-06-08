-- This module is modelling the example test/EtaRecordsUnit.agda but in Agda Core

module Agda.Core.TestEtaRecordsUnit where

open import Agda.Core.Prelude

open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.TCM.TCM
open import Agda.Core.Rules.Untyped.Typing
open import Agda.Core.Checkers.Untyped.TypeCheck
open import Agda.Core.Checkers.Untyped.Converter
open import Agda.Core.Rules.Untyped.Conversion
open import Agda.Core.Rules.Unification
open import Agda.Core.Checkers.Unifier

private variable
  x y : Name
  α : Scope Name

datas = mempty ▸ "_≡_"
records = mempty ▸ "EmptyRecord"

instance
  globals : Globals
  globals = record
    { defScope = mempty ▸ "etaExpandEmptyRec" ▸ "testUnitConvPositive"
    ; dataScope = datas
    ; recScope = records
    ; dataParScope = λ where
      -- _≡_
      _ -> "A" ◂ "x" ◂ mempty --(A : Set) (x : A)
    ; dataIxScope = λ where
      -- _≡_
      _ -> "y" ◂ mempty
    ; dataConstructors = λ where
      -- _≡_
      _ -> "refl" ◂ mempty
    ; dataFieldScope = λ where 
      -- refl of _≡_ 
      _ → mempty
    ; recParScope = λ where 
      -- EmptyRecord
      _ -> mempty
    ; recFieldScope = λ where 
      -- EmptyRecord
      _ -> mempty
    ; recCon = λ where 
      _ → "this name is irrelevant and not used in the typechecker"
    }
open module @0 G = Globals globals

instance
  {-# TERMINATING #-}
  fuel : Fuel
  fuel = More {{fuel}}

nameTestUnitConvPositive  : NameIn defScope
nameTestUnitConvPositive  = ⟨ "testUnitConvPositive" ⟩ Zero ⟨ (IsZero refl) ⟩

nameEtaExpandEmptyRec : NameIn defScope
nameEtaExpandEmptyRec = ⟨ "etaExpandEmptyRec" ⟩ (Suc Zero ⟨ IsSuc (IsZero refl) ⟩)

nameEquiv : NameData
nameEquiv = ⟨ "_≡_" ⟩ (Zero ⟨ IsZero refl ⟩)

nameEmptyRecord : NameRec
nameEmptyRecord = ⟨ "EmptyRecord" ⟩ (Zero ⟨ IsZero refl ⟩)


nameRefl : NameDataCon nameEquiv
nameRefl = ⟨ "refl" ⟩ (Zero ⟨ IsZeroR refl ⟩)

opaque
  unfolding ScopeThings RScope

  sigDataInstance : (d : NameData) → Datatype d
  -- _≡_
  sigDataInstance (⟨ _ ⟩ (Zero ⟨ IsZero refl ⟩)) = record
    { dataSort = STyp 0
    ; dataParTel = "A" ∶ (El (STyp 1) (TSort (STyp 0))) -- (A : Set)
        ◂ ("x" ∶ (El (STyp 0) (TVar (⟨ "A" ⟩ (Zero ⟨ IsZero refl ⟩)))) ◂ EmptyTel) -- "x : A" 
    ; dataIxTel = "y" ∶ El (STyp 0) (TVar (⟨ "x" ⟩ (Zero ⟨ IsZero refl ⟩))) ◂ EmptyTel -- "y : A"
    ; dataConstructors = [] --empty because only used on the Haskell side
    }
  sigDataInstance (⟨ _ ⟩ (Suc _ ⟨ IsSuc () ⟩))

  sigConsInstance : (d : NameData) (c : NameDataCon d) → DataConstructor {d = d} c
  -- _≡_ refl
  sigConsInstance (⟨ proj₃ ⟩ (Zero ⟨ proof₁ ⟩)) (⟨ proj₄ ⟩ (Zero ⟨ proof₂ ⟩)) = record { 
        conIndTel = EmptyTel
    ; conIx = TSCons (TVar (⟨ "x" ⟩ (Zero ⟨ IsZero refl ⟩))) TSNil }
  sigConsInstance (⟨ proj₃ ⟩ (Zero ⟨ proof₁ ⟩)) (⟨ proj₄ ⟩ (Suc value₁ ⟨ IsSucR () ⟩))
  sigConsInstance (⟨ proj₃ ⟩ (Suc value₁ ⟨ IsSuc () ⟩)) c

  sigRecsInstance : (recordName : NameRec) → Record recordName
  --EmptyRecord
  sigRecsInstance (⟨ _ ⟩ (Zero ⟨ IsZero refl ⟩)) = record { 
    recSort = STyp 0 ; 
    recParTel = ⌈⌉ ; 
    recConArgTel = ⌈⌉ }
  sigRecsInstance (⟨ _ ⟩ (Suc _ ⟨ IsSuc () ⟩))

  sigDefInstance : (f : NameIn defScope)  → Type mempty × SigDefinition
  --testUnitConvPositive 
  sigDefInstance (⟨ _ ⟩ (Zero ⟨ IsZero refl ⟩)) = 
    -- (a b : EmptyRecord) → a ≡ b
    El (STyp 0) (TPi "a" (El (STyp 0) (TRec nameEmptyRecord ⌈⌉))
      (El (STyp 0) (TPi "b" (El (STyp 0) (TRec nameEmptyRecord ⌈⌉)) 
        (El (STyp 0) (TData nameEquiv 
          (TSCons (TRec nameEmptyRecord ⌈⌉) (TSCons (TVar (⟨ "a" ⟩ (Suc Zero ⟨ IsSuc (IsZero refl) ⟩))) TSNil)) 
          (TSCons (TVar (⟨ "b" ⟩ (Zero ⟨ IsZero refl ⟩))) TSNil)))))) 
    ,
    -- λ a b → refl 
    FunctionDef (TLam "a" (TLam "b" (TDataCon {d = nameEquiv} nameRefl ⌈⌉)))
  --etaExpandEmptyRec
  sigDefInstance (⟨ _ ⟩ (Suc Zero ⟨ IsSuc proof ⟩)) = 
    --(a : EmptyRecord) → (a ≡ EmptyRecord.constructor)
    El (STyp 0) (TPi "a" (El (STyp 0) (TRec nameEmptyRecord ⌈⌉)) 
      (El (STyp 0) (TData nameEquiv 
        (TSCons (TRec nameEmptyRecord ⌈⌉) (TSCons (TVar (⟨ "a" ⟩ (Zero ⟨ IsZero refl ⟩))) TSNil)) 
        (TSCons (TRecCon nameEmptyRecord ⌈⌉) TSNil)))) 
    ,
    -- λ a → refl 
    FunctionDef (TLam "a" (TDataCon {d = nameEquiv} nameRefl ⌈⌉))
  sigDefInstance (⟨ _ ⟩ (Suc (Suc _) ⟨ IsSuc (IsSuc ()) ⟩))


instance
  sig : Signature
  sig .sigData = sigDataInstance
  sig .sigDefs n = sigDefInstance n
  sig .sigRecs = sigRecsInstance
  sig .sigCons d c = sigConsInstance d c

module TestTypechecker (@0 x y z : Name) where
  opaque
    -- TODO (atejandev): make this list of unfolding terms s.t. it is the minimum one required by each test
    unfolding ScopeThings AllNameCon rScopeToRScopeNameInR extendEnvironment addTel subToSubst substExtScope caseBsNil caseBsCons caseTermSNil caseTermSCons termSrepeat sigRecsInstance lookupNameRinTel etaProjTermS


    -- λ a → refl [body of etaExpandEmptyRec]
    testTerm₁ : Term α
    testTerm₁ = (TLam "a" (TDataCon {d = nameEquiv} nameRefl ⌈⌉))

    -- (a : EmptyRecord) → (a ≡ EmptyRecord.constructor) [type of etaExpandEmptyRec]
    testType₁ : Type α
    testType₁ = El (STyp 0) (TPi "a" (El (STyp 0) (TRec nameEmptyRecord ⌈⌉)) 
      (El (STyp 0) (TData nameEquiv 
        (TSCons (TRec nameEmptyRecord ⌈⌉) (TSCons (TVar (⟨ "a" ⟩ (Zero ⟨ IsZero refl ⟩))) TSNil)) 
        (TSCons (TRecCon nameEmptyRecord ⌈⌉) TSNil))))

    testTC₁ : Either TCError (CtxEmpty ⊢ testTerm₁ ∶ testType₁)
    testTC₁ = runTCM (checkType CtxEmpty testTerm₁ testType₁) (MkTCEnv (sing sig) fuel)

    @0 testTC₁Prop : Set
    proofOftestTC₁Prop : testTC₁Prop

    -- An implementation of untyped conversion should produce Left
    testTC₁Prop = testTC₁ ≡ Left "Cannot apply untyped eta-conversion 
  for records on a record whose 
  constructor takes zero arguments"
    proofOftestTC₁Prop = refl

