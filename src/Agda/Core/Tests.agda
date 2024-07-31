
module Agda.Core.Tests where

open import Haskell.Prelude hiding (All)

open import Haskell.Extra.Erase
open import Haskell.Law.Equality
open import Haskell.Extra.Refinement

open import Scope
open import Utils.Tactics using (auto)

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Utils
open import Agda.Core.Syntax
open import Agda.Core.Signature
open import Agda.Core.Reduce

open import Agda.Core.Context
open import Agda.Core.TCM
open import Agda.Core.Typing
open import Agda.Core.Typechecker

private variable
  x y : Name
  α : Scope Name

instance
  top : In x (x ◃ α)
  top = inHere

  pop : {{x ∈ α}} → x ∈ (y ◃ α)
  pop {{p}} = inThere p

datas = singleton "Bool"

cons = bind "true" $ bind "false" mempty

instance
  globals : Globals
  globals = record
    { defScope = mempty
    ; dataScope = datas
    ; dataParScope = λ _ → mempty
    ; dataIxScope = λ _ → mempty
    ; conScope = cons
    ; fieldScope = λ _ → mempty
    }

boolcons : (c : NameIn cons)
         → Σ (proj₁ c ∈ cons) (λ cp → Constructor mempty mempty (⟨ _ ⟩ cp))
boolcons (⟨ c ⟩ cp) = lookupAll
  {p = λ c → Σ (c ∈ cons) (λ cp → Constructor mempty mempty (⟨ _ ⟩ cp))}
  (allJoin (allSingl (inHere
                     , record { conTelescope = EmptyTel
                              ; conIndices = SNil } )) $
   allJoin (allSingl (inThere inHere
                     , record { conTelescope = EmptyTel
                              ; conIndices = SNil })) $
   allEmpty)
  cp

bool : Datatype mempty mempty
bool .dataConstructorScope = cons
bool .dataSort = STyp 0
bool .dataParameterTel = EmptyTel
bool .dataIndexTel = EmptyTel
bool .dataConstructors = boolcons

instance
  sig : Signature
  sig .sigData = λ _ → bool
  sig .sigDefs = nameInEmptyCase

instance
  {-# TERMINATING #-}
  fuel : Fuel
  fuel = More {{fuel}}

opaque
  unfolding ScopeThings

  `true : Term α
  `true = TCon (⟨ "true" ⟩ inHere) SNil
  `false : Term α
  `false = TCon (⟨ "false" ⟩ inThere inHere) SNil

module TestReduce (@0 x y z : Name) where

  opaque
    unfolding ScopeThings `true `false

    testTerm₁ : Term α
    testTerm₁ = apply (TLam x (TVar (⟨ x ⟩ inHere))) (TSort (STyp 0))

    @0 testProp₁ : Set
    testProp₁ = reduceClosed (rezz sig) testTerm₁ ≡ Just (TSort (STyp 0))

    test₁ : testProp₁
    test₁ = refl

    testTerm₂ : Term α
    testTerm₂ = TCase {x = "condition"} `true
                                  (BsCons (BBranch (⟨ "true" ⟩ inHere) (rezz _) `false)
                                  (BsCons (BBranch (⟨ "false" ⟩ inThere inHere) (rezz _) `true)
                                   BsNil))
                                  (El (STyp 0) (TData (⟨ "Bool" ⟩ inHere) SNil SNil))

    @0 testProp₂ : Set
    testProp₂ = reduceClosed (rezz sig) testTerm₂ ≡ Just `false

    test₂ : testProp₂
    test₂ = refl

module TestTypechecker (@0 x y z : Name) where

  opaque
    unfolding ScopeThings `true `false

    testTerm₁ : Term α
    testTerm₁ = TLam x (TVar (⟨ x ⟩ inHere))

    testType₁ : Type α
    testType₁ = El (STyp 0) (TPi y (El (STyp 0) (TData (⟨ "Bool" ⟩ inHere) SNil SNil)) (El (STyp 0) (TData (⟨ "Bool" ⟩ inHere) SNil SNil)))

    testTC₁ : Either TCError (CtxEmpty ⊢ testTerm₁ ∶ testType₁)
    testTC₁ = runTCM (checkType CtxEmpty testTerm₁ testType₁) (MkTCEnv (rezz _) fuel)

    @0 testProp₁ : Set
    test₁ : testProp₁

    testProp₁ = testTC₁ ≡ Right _
    test₁ = refl


-- -}
