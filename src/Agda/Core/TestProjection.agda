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
records = mempty ▸ "ContainerRecord" ▸ "Σ"

instance
  globals : Globals
  globals = record
    { defScope = mempty ▸ "containerX" ▸ "sigmaRecordElement" ▸ "sigmaRecordElementProjSnd"
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
      (⟨ _ ⟩ (Zero ⟨ _ ⟩)) → "a" ◂ "b" ◂ mempty
      -- ContainerRecord
      (⟨ _ ⟩ (Suc _ ⟨ _ ⟩)) → mempty
    ; recFieldScope = λ where 
      -- Σ
      (⟨ proj₃ ⟩ (Zero ⟨ proof₁ ⟩)) → "fst" ◂ "snd" ◂ mempty
      -- ContainerRecord
      (⟨ proj₃ ⟩ (Suc _ ⟨ proof₁ ⟩)) → "theProj" ◂ mempty 
    ; recCon = λ where 
      _ → "this name is irrelevant and not used in the typechecker"
    }
open module @0 G = Globals globals

nameContainerX : NameIn defScope
nameContainerX = ⟨ "containerX" ⟩ (Suc (Suc Zero) ⟨ IsSuc (IsSuc (IsZero refl)) ⟩)

nameSigmaRecordElement : NameIn defScope
nameSigmaRecordElement = ⟨ "sigmaRecordElement" ⟩ (Suc Zero ⟨ IsSuc (IsZero refl) ⟩)

nameSigmaRecordElementProjSnd : NameIn defScope
nameSigmaRecordElementProjSnd = ⟨ "sigmaRecordElementProjSnd" ⟩ (Zero ⟨ IsZero refl ⟩)

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

nameSigma : NameRec
nameSigma = ⟨ "Σ" ⟩ (Zero ⟨ IsZero refl ⟩)

nameContainerRecord : NameRec 
nameContainerRecord = ⟨ "ContainerRecord" ⟩ (Suc Zero ⟨ IsSuc (IsZero refl) ⟩)

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
sigDataInstance (⟨ proj₃ ⟩ (Suc (Suc _) ⟨ proof₁ ⟩)) = Datatype.constructor (STyp 0) EmptyTel EmptyTel []

sigDefInstance : (f : NameIn defScope)  → Type mempty × SigDefinition
--sigmaRecordElementProjSnd (corresponds to Zero)
sigDefInstance (⟨ _ ⟩ (Zero ⟨ _ ⟩)) = 
  --Vector Bool (Suc (Suc Zero))
  El (STyp 0) (TData nameVector
    (TSCons (TData nameBool TSNil TSNil) TSNil) 
    (TSCons ((TDataCon {d = nameNat} nameSuc 
      (TSCons (TDataCon {d = nameNat} nameSuc 
        (TSCons (TDataCon {d = nameNat} nameZero TSNil) TSNil)) TSNil))) TSNil)) 
  , 
  --sigmaRecordElement .Σ.snd
  FunctionDef (TProj {rn = nameSigma} (TDef (⟨ "sigmaRecordElement" ⟩ (Suc Zero ⟨ IsSuc (IsZero refl) ⟩))) 
    (⟨ "snd" ⟩ (Suc Zero ⟨ IsSucR (IsZeroR refl) ⟩)))
--sigmaRecordElement (corresponds to (Suc Zero))
sigDefInstance (⟨ proj₃ ⟩ (Suc Zero ⟨ proof₁ ⟩)) = 
  -- Σ Nat (λ n → (Vector Bool n))
  El (STyp 0) (TRec nameSigma
    (TSCons (TData nameNat TSNil TSNil) 
    (TSCons (TLam "n" (TData nameVector 
      (TSCons (TData nameBool TSNil TSNil) TSNil) 
      (TSCons (TVar (⟨ "n" ⟩ (Zero ⟨ IsZero refl ⟩))) TSNil))) TSNil)))
  ,
  --Σ.constructor (Suc (Suc Zero)) (Cons False (Cons False Nil)) 
  FunctionDef (TRecCon nameSigma 
    -- Suc (Suc Zero)
    (TSCons (TDataCon {d = nameNat} nameSuc 
      (TSCons (TDataCon {d = nameNat} nameSuc 
        (TSCons (TDataCon {d = nameNat} nameZero TSNil) TSNil)) TSNil)) 
    -- (VCons (Suc Zero) False (VCons Zero False Nil))
    (TSCons (TDataCon {d = nameVector} nameCons -- VCons
      (TSCons (TDataCon {d = nameNat} nameSuc (TSCons (TDataCon {d = nameNat} nameZero TSNil) TSNil)) 
      (TSCons (TDataCon {d = nameBool} nameFalse TSNil) 
      (TSCons (TDataCon {d = nameVector} nameCons 
        (TSCons (TDataCon {d = nameNat} nameZero TSNil) 
        (TSCons (TDataCon {d = nameBool} nameFalse TSNil) 
        (TSCons (TDataCon {d = nameVector} nameNil TSNil) TSNil)))) TSNil)))) TSNil)))
-- containerX (corresponds to Suc Suc Zero)
sigDefInstance (⟨ _ ⟩ (Suc (Suc _) ⟨ _ ⟩)) = 
  -- ContainerRecord 
  El (STyp 0) (TRec nameContainerRecord TSNil)
  , 
  --  (ContainerRecord.constructor [ False ]) .ContainerRecord.theProj
  FunctionDef (TProj {rn = nameContainerRecord} 
        (TRecCon nameContainerRecord (TSCons (TDataCon {d = nameBool} nameFalse TSNil) TSNil)) 
        (⟨ "theProj" ⟩ (Zero ⟨ IsZeroR refl ⟩)))

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
  sigConsInstance (⟨ _ ⟩ (Suc Zero ⟨ _ ⟩)) (⟨ _ ⟩ (Suc Zero ⟨ _ ⟩)) = DataConstructor.constructor 
    ("base" ∶ El (STyp 0) (TData nameNat TSNil TSNil) ◂ EmptyTel)
    TSNil
  -- Bool True
  sigConsInstance (⟨ _ ⟩ (Suc (Suc Zero) ⟨ _ ⟩)) (⟨ _ ⟩ (Zero ⟨ _ ⟩)) = DataConstructor.constructor EmptyTel TSNil
  -- Bool False
  sigConsInstance (⟨ _ ⟩ (Suc (Suc Zero) ⟨ _ ⟩)) (⟨ _ ⟩ (Suc Zero ⟨ _ ⟩)) = DataConstructor.constructor EmptyTel TSNil

  -- Does not correspond to anything
  sigConsInstance (⟨ _ ⟩ (Suc Zero ⟨ proof₁ ⟩)) (⟨ _ ⟩ (Suc (Suc value₂) ⟨ IsSucR (IsSucR ()) ⟩))
  sigConsInstance (⟨ _ ⟩ (Suc (Suc Zero) ⟨ proof₁ ⟩)) (⟨ proj₃ ⟩ (Suc (Suc value₂) ⟨ IsSucR (IsSucR ()) ⟩))
  sigConsInstance (⟨ _ ⟩ (Suc (Suc (Suc value₁)) ⟨ IsSuc (IsSuc (IsSuc ())) ⟩)) (⟨ proj₃ ⟩ (value₂ ⟨ proof₂ ⟩))

  sigRecsInstance : (recordName : NameRec) → Record recordName
  --Σ
  sigRecsInstance (⟨ _ ⟩ (Zero ⟨ _ ⟩)) = Record.constructor (STyp 0)
            -- (a : Set) (b : a → Set)
            ("a" ∶ El (STyp 1) (TSort (STyp 0)) --(a : Set)
            ◂ ("b" ∶ El (STyp 1) -- (b : a → Set) (atejandev: I don't know whether this sort should be STyp 0 or STyp 1). I should turn back here if I have problems with getting this test accepted
                (TPi "dummy" 
                  (El (STyp 0) (TVar (⟨ "a" ⟩ (Zero ⟨ IsZero refl ⟩)))) --a
                  (El (STyp 1) (TSort (STyp 0)))) -- → Set
            ◂ EmptyTel)) 
            -- (fst : a) (snd : b fst)
            ("fst" ∶ El (STyp 0) (TVar (⟨ "a" ⟩ inThere inHere)) 
            ◂ ("snd" ∶ El (STyp 0) (TApp (TVar ((⟨ "b" ⟩ inThere inHere))) (TVar ((⟨ "fst" ⟩ inHere)))) 
            ◂ EmptyTel))
--ContainerRecord
  sigRecsInstance (⟨ _ ⟩ ((Suc _) ⟨ _ ⟩)) = record 
    { recSort = STyp 0 ; recParTel = EmptyTel ; recConArgTel = "theProj" ∶ El (STyp 0) (TData nameBool TSNil TSNil) ◂ EmptyTel }

instance
  sig : Signature
  sig .sigData = sigDataInstance
  sig .sigDefs n = sigDefInstance n
  sig .sigRecs = sigRecsInstance
  sig .sigCons d c = sigConsInstance d c


module TestTypechecker (@0 x y z : Name) where


  opaque
    -- TODO (atejandev): make this list of unfolding terms s.t. it is the minimum one required by each test
    unfolding ScopeThings AllNameCon rScopeToRScopeNameInR extendEnvironment addTel subToSubst substExtScope caseBsNil caseBsCons caseTermSNil caseTermSCons termSrepeat sigRecsInstance

    --Σ.constructor (Suc (Suc Zero)) (Cons False (Cons False Nil)) 
    testTerm₁_sub : Term α
    testTerm₁_sub = TRecCon nameSigma 
      -- Suc (Suc Zero)
      (TSCons (TDataCon {d = nameNat} nameSuc 
        (TSCons (TDataCon {d = nameNat} nameSuc 
          (TSCons (TDataCon {d = nameNat} nameZero TSNil) TSNil)) TSNil)) 
      -- (VCons (Suc Zero) False (VCons Zero False Nil))
      (TSCons (TDataCon {d = nameVector} nameCons -- VCons
        (TSCons (TDataCon {d = nameNat} nameSuc (TSCons (TDataCon {d = nameNat} nameZero TSNil) TSNil)) 
        (TSCons (TDataCon {d = nameBool} nameFalse TSNil) 
        (TSCons (TDataCon {d = nameVector} nameCons 
          (TSCons (TDataCon {d = nameNat} nameZero TSNil) 
          (TSCons (TDataCon {d = nameBool} nameFalse TSNil) 
          (TSCons (TDataCon {d = nameVector} nameNil TSNil) TSNil)))) TSNil)))) TSNil))

    --Σ Nat (λ n → (Vector Bool n))
    testType₁_sub : Type α 
    testType₁_sub = El (STyp 0) (TRec nameSigma
      (TSCons (TData nameNat TSNil TSNil) 
      (TSCons (TLam "n" (TData nameVector 
        (TSCons (TData nameBool TSNil TSNil) TSNil) 
        (TSCons (TVar (⟨ "n" ⟩ (Zero ⟨ IsZero refl ⟩))) TSNil))) TSNil)))

    testTC₁_sub : Either TCError (CtxEmpty ⊢ testTerm₁_sub ∶ testType₁_sub)
    testTC₁_sub = runTCM (checkType CtxEmpty testTerm₁_sub testType₁_sub) (MkTCEnv (sing sig) fuel)

    testTC₁_sub_as_TDef : Either TCError (CtxEmpty ⊢ TDef nameSigmaRecordElement  ∶ testType₁_sub)
    testTC₁_sub_as_TDef = runTCM (checkType CtxEmpty (TDef nameSigmaRecordElement) testType₁_sub) (MkTCEnv (sing sig) fuel)

    -- nameContainerX .theProj
    testTCProj₀₁_term : Term α
    testTCProj₀₁_term = TProj {rn = nameContainerRecord} (TDef nameContainerX) (⟨ "theProj" ⟩ (Zero ⟨ IsZeroR refl ⟩))

    --Bool
    testTCProj₀₁_type : Type α
    testTCProj₀₁_type = (El (STyp 0) (TData nameBool TSNil TSNil))
    
    testTCProj₀₁ : Either TCError
      (CtxEmpty ⊢ testTCProj₀₁_term ∶ testTCProj₀₁_type)
    testTCProj₀₁ = runTCM (checkType CtxEmpty testTCProj₀₁_term testTCProj₀₁_type) (MkTCEnv (sing sig) fuel)


    

    --sigmaRecordElement .Σ.snd
    testTProjTerm₁ : Term α
    testTProjTerm₁ = (TProj {rn = nameSigma} (TDef (⟨ "sigmaRecordElement" ⟩ (Suc Zero ⟨ IsSuc (IsZero refl) ⟩))) 
      (⟨ "snd" ⟩ (Suc Zero ⟨ IsSucR (IsZeroR refl) ⟩)))

    --Vector Bool (Suc (Suc Zero))
    testTProjResultType₁ : Type α
    testTProjResultType₁ = El (STyp 0) (TData nameVector
      (TSCons (TData nameBool TSNil TSNil) TSNil) 
      (TSCons ((TDataCon {d = nameNat} nameSuc 
        (TSCons (TDataCon {d = nameNat} nameSuc 
          (TSCons (TDataCon {d = nameNat} nameZero TSNil) TSNil)) TSNil))) TSNil)) 

    testTCProj₁ : Either TCError (CtxEmpty ⊢ testTProjTerm₁ ∶ testTProjResultType₁)
    testTCProj₁ = runTCM (checkType CtxEmpty testTProjTerm₁ testTProjResultType₁) (MkTCEnv (sing sig) fuel)

    --sigmaRecordElement .Σ.fst
    testTProjTerm₂ : Term α
    testTProjTerm₂ = (TProj {rn = nameSigma} (TDef (⟨ "sigmaRecordElement" ⟩ (Suc Zero ⟨ IsSuc (IsZero refl) ⟩))) 
      (⟨ "fst" ⟩ (Zero ⟨ (IsZeroR refl) ⟩)))

    -- Nat
    testTProjResultType₂ : Type α
    testTProjResultType₂ = El (STyp 0) (TData nameNat TSNil TSNil)


    testTCProj₂ : Either TCError (CtxEmpty ⊢ testTProjTerm₂ ∶ testTProjResultType₂)
    testTCProj₂ = runTCM (checkType CtxEmpty testTProjTerm₂ testTProjResultType₂) (MkTCEnv (sing sig) fuel)



    @0 testProp1_sub : Set
    test₁_sub : testProp1_sub

    testProp1_sub = testTC₁_sub ≡ Right _
    test₁_sub = refl


    @0 testPropTC₁_sub_as_TDef : Set 
    test_sub_as_TDef : testPropTC₁_sub_as_TDef

    testPropTC₁_sub_as_TDef = testTC₁_sub_as_TDef ≡ Right _
    test_sub_as_TDef = refl


    @0 testTCProj₀₁Prop : Set
    proofOftestTCProj₀₁Prop : testTCProj₀₁Prop

    testTCProj₀₁Prop = testTCProj₀₁ ≡ Right _
    proofOftestTCProj₀₁Prop = refl
  

    
    @0 testTCProj₁Prop : Set
    testTCProj₁Prop₁ : testTCProj₁Prop

    testTCProj₁Prop = testTCProj₁ ≡ Right _
    testTCProj₁Prop₁ = {!!}



    @0 testTCProj₂Prop : Set 
    proofOftestTCProj₂Prop : testTCProj₂Prop

    testTCProj₂Prop = testTCProj₂ ≡ Right _
    proofOftestTCProj₂Prop = refl
