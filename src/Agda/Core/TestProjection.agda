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

boolConsRSC = "True" ◂ "False" ◂ mempty

cons = mempty ◂▸ boolConsRSC

instance
  globals : Globals
  globals = record
    { defScope = mempty
    ; dataScope = datas
    ; recScope = mempty
    ; dataParScope = λ _ → mempty
    ; dataIxScope = λ _ → mempty
    ; dataConstructors = λ _ → boolConsRSC
    ; dataFieldScope = λ _ → mempty
    ; recParScope = λ _ → mempty 
    ; recFieldScope = λ _ → mempty
    ; recCon = λ _ → mempty
    }
open module @0 G = Globals globals

boolsigcons : {@0 d : NameData} (c : NameDataCon d) → DataConstructor {d = d} c
boolsigcons _  = record { conIndTel = EmptyTel; conIx = TSNil }


opaque
  unfolding ScopeThings

  nameBool : NameIn datas
  nameBool = {!!}

instance
  sig : Signature
  sig .sigData = λ _ → record { dataSort = STyp 0 ; dataParTel = EmptyTel ; dataIxTel = EmptyTel; dataConstructors = []}
  sig .sigDefs n = nameInEmptyCase n
  sig .sigRecs rn = nameInEmptyCase rn
  sig .sigCons d c = boolsigcons {d = d} c

instance
  {-# TERMINATING #-}
  fuel : Fuel
  fuel = More {{fuel}}

opaque
  unfolding ScopeThings nameBool

  nameTrue : NameDataCon nameBool
  nameTrue = ⟨ "True" ⟩ inRHere
  nameFalse : NameDataCon nameBool
  nameFalse = ⟨ "False" ⟩ inRThere inRHere

  `true : Term α
  `true = TDataCon {d = nameBool} nameTrue TSNil
  `false : Term α
  `false = TDataCon {d = nameBool} nameFalse TSNil

module TestTypechecker (@0 x y z : Name) where

  opaque
    unfolding ScopeThings `true `false

    testTerm₁ : Term α
    testTerm₁ = TLam x (TVar (⟨ x ⟩ inHere))

    testType₁ : Type α
    testType₁ = El (STyp 0) (TPi y (El (STyp 0) (TData (⟨ "Bool" ⟩ inHere) TSNil TSNil)) (El (STyp 0) (TData (⟨ "Bool" ⟩ inHere) TSNil TSNil)))

    testTC₁ : Either TCError (CtxEmpty ⊢ testTerm₁ ∶ testType₁)
    testTC₁ = runTCM (checkType CtxEmpty testTerm₁ testType₁) (MkTCEnv (sing _) fuel)

    @0 testProp₁ : Set
    test₁ : testProp₁

    testProp₁ = testTC₁ ≡ Right _
    test₁ = refl

