-- Regression test: typing a projection applied to a /neutral/ record term
-- (here, a lambda-bound variable).  Previously `inferProj` required the
-- projected term to reduce to a record constructor (`reduceToTRecCon`), so a
-- projection on a variable was wrongly rejected.  It should instead fall back
-- to the neutral rule `TyProjNeutral`, using the η-expansion of the term as
-- the record's fields.
--
-- This module models the surface-level program
--
--   data Bool : Set where True False : Bool
--   record R : Set where field f : Bool
--   getF : (r : R) → Bool
--   getF = λ r → r .f
--
-- in Agda Core, and checks that the body of `getF` is well-typed.

module Agda.Core.TestProjectionNeutral where

open import Agda.Core.Prelude

open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.TCM.TCM
open import Agda.Core.Rules.Typing
open import Agda.Core.Checkers.TypeCheck
open import Agda.Core.Rules.Conversion

private variable
  α : Scope Name

datas   = mempty ▸ "Bool"
records = mempty ▸ "R"

instance
  globals : Globals
  globals = record
    { defScope = mempty ▸ "getF"
    ; dataScope = datas
    ; recScope = records
    ; dataParScope = λ where
      _ -> mempty
    ; dataIxScope = λ where
      _ -> mempty
    ; dataConstructors = λ where
      -- Bool
      _ -> "True" ◂ "False" ◂ mempty
    ; dataFieldScope = λ where
      -- True and False have no fields
      _ → mempty
    ; recParScope = λ where
      -- R
      _ -> mempty
    ; recFieldScope = λ where
      -- R
      _ -> "f" ◂ mempty
    ; recCon = λ where
      _ → "this name is irrelevant and not used in the typechecker"
    }
open module @0 G = Globals globals

instance
  {-# TERMINATING #-}
  fuel : Fuel
  fuel = More {{fuel}}

nameBool : NameData
nameBool = ⟨ "Bool" ⟩ (Zero ⟨ IsZero refl ⟩)

nameR : NameRec
nameR = ⟨ "R" ⟩ (Zero ⟨ IsZero refl ⟩)

nameGetF : NameIn defScope
nameGetF = ⟨ "getF" ⟩ (Zero ⟨ IsZero refl ⟩)

nameF : NameProj nameR
nameF = ⟨ "f" ⟩ (Zero ⟨ IsZeroR refl ⟩)

opaque
  unfolding ScopeThings RScope

  sigDataInstance : (d : NameData) → Datatype d
  -- Bool
  sigDataInstance (⟨ _ ⟩ (Zero ⟨ _ ⟩)) =
    Datatype.constructor (STyp 0) EmptyTel EmptyTel []
  sigDataInstance (⟨ _ ⟩ (Suc _ ⟨ IsSuc () ⟩))

  sigConsInstance : (d : NameData) (c : NameDataCon d) → DataConstructor {d = d} c
  -- Bool True / False
  sigConsInstance (⟨ _ ⟩ (Zero ⟨ _ ⟩)) (⟨ _ ⟩ (Zero ⟨ _ ⟩)) =
    DataConstructor.constructor EmptyTel TSNil
  sigConsInstance (⟨ _ ⟩ (Zero ⟨ _ ⟩)) (⟨ _ ⟩ (Suc Zero ⟨ _ ⟩)) =
    DataConstructor.constructor EmptyTel TSNil
  sigConsInstance (⟨ _ ⟩ (Zero ⟨ _ ⟩)) (⟨ _ ⟩ (Suc (Suc _) ⟨ IsSucR (IsSucR ()) ⟩))
  sigConsInstance (⟨ _ ⟩ (Suc _ ⟨ IsSuc () ⟩)) c

  sigRecsInstance : (recordName : NameRec) → Record recordName
  -- R
  sigRecsInstance (⟨ _ ⟩ (Zero ⟨ _ ⟩)) = record
    { recSort = STyp 0
    ; recParTel = EmptyTel
    ; recConArgTel = "f" ∶ El (STyp 0) (TData nameBool TSNil TSNil) ◂ EmptyTel
    }
  sigRecsInstance (⟨ _ ⟩ (Suc _ ⟨ IsSuc () ⟩))

  sigDefInstance : (f : NameIn defScope)  → Type mempty × SigDefinition
  -- getF : (r : R) → Bool
  sigDefInstance (⟨ _ ⟩ (Zero ⟨ _ ⟩)) =
    El (STyp 0) (TPi "r" (El (STyp 0) (TRec nameR TSNil))
                  (El (STyp 0) (TData nameBool TSNil TSNil)))
    ,
    -- getF = λ r → r .f
    FunctionDef (TLam "r" (TProj {rn = nameR} (TVar (⟨ "r" ⟩ (Zero ⟨ IsZero refl ⟩))) nameF))
  sigDefInstance (⟨ _ ⟩ (Suc _ ⟨ IsSuc () ⟩))

instance
  sig : Signature
  sig .sigData = sigDataInstance
  sig .sigDefs n = sigDefInstance n
  sig .sigRecs = sigRecsInstance
  sig .sigCons d c = sigConsInstance d c

module TestTypechecker where
  opaque
    unfolding ScopeThings AllNameCon rScopeToRScopeNameInR extendEnvironment addTel subToSubst substExtScope caseBsNil caseBsCons caseTermSNil caseTermSCons termSrepeat sigRecsInstance lookupNameRinTel etaProjTermS

    -- λ r → r .f
    testTerm : Term α
    testTerm = TLam "r" (TProj {rn = nameR} (TVar (⟨ "r" ⟩ (Zero ⟨ IsZero refl ⟩))) nameF)

    -- (r : R) → Bool
    testType : Type α
    testType = El (STyp 0) (TPi "r" (El (STyp 0) (TRec nameR TSNil))
                             (El (STyp 0) (TData nameBool TSNil TSNil)))

    testTC : Either TCError (CtxEmpty ⊢ testTerm ∶ testType)
    testTC = runTCM (checkType CtxEmpty testTerm testType) (MkTCEnv (sing sig) fuel)

    -- The whole point: a projection on a neutral (bound) variable is accepted.
    @0 testProp : Set
    testProof : testProp

    testProp = testTC ≡ Right _
    testProof = refl
