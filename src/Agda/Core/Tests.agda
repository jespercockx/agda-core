
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
open import Agda.Core.Unification
open import Agda.Core.Unifier

private variable
  x y : Name
  α : Scope Name

instance
  top : x ∈  (α ▸ x)
  top = inHere

  pop : {{x ∈ α}} → x ∈  (α ▸ y)
  pop {{p}} = inThere p

datas = singleton "Bool"

cons = mempty ▸ "false" ▸ "true"

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

boolcons : ((⟨ c ⟩ cp) : NameIn cons)
         → Σ (c ∈ cons) (λ cp → Constructor mempty mempty (⟨ c ⟩ cp))
boolcons (⟨ c ⟩ cp) = lookupAll
  {p = λ c → Σ (c ∈ cons) (λ cp → Constructor mempty mempty (⟨ c ⟩ cp))}
  (let x = allJoin allEmpty (allSingl (inThere inHere
                     , record { conIndTel = EmptyTel
                              ; conIx = TSNil })) in
    allJoin x (allSingl (inHere
                     , record { conIndTel = EmptyTel
                              ; conIx = TSNil } ))
   )
  cp

bool : Datatype mempty mempty
bool .dataConstructorScope = cons
bool .dataSort = STyp 0
bool .dataParTel = EmptyTel
bool .dataIxTel = EmptyTel
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
  `true = TCon (⟨ "true" ⟩ inHere) TSNil
  `false : Term α
  `false = TCon (⟨ "false" ⟩ inThere inHere) TSNil

module TestReduce (@0 x y z : Name) where

  opaque
    unfolding ScopeThings `true `false

    testTerm₁ : Term α
    testTerm₁ = TApp (TLam x (TVar (⟨ x ⟩ inHere))) (TSort (STyp 0))

    @0 testProp₁ : Set
    testProp₁ = reduceClosed (rezz sig) testTerm₁ ≡ Just (TSort (STyp 0))

    test₁ : testProp₁
    test₁ = refl

    testTerm₂ : Term α
    testTerm₂ = TCase {x = "condition"} (⟨ "Bool" ⟩ inHere) (rezz _) `true
                                  (BsCons (BBranch (⟨ "true" ⟩ inHere) (rezz _) `false)
                                  (BsCons (BBranch (⟨ "false" ⟩ inThere inHere) (rezz _) `true)
                                   BsNil))
                                  (El (STyp 0) (TData (⟨ "Bool" ⟩ inHere) TSNil TSNil))

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
    testType₁ = El (STyp 0) (TPi y (El (STyp 0) (TData (⟨ "Bool" ⟩ inHere) TSNil TSNil)) (El (STyp 0) (TData (⟨ "Bool" ⟩ inHere) TSNil TSNil)))

    testTC₁ : Either TCError (CtxEmpty ⊢ testTerm₁ ∶ testType₁)
    testTC₁ = runTCM (checkType CtxEmpty testTerm₁ testType₁) (MkTCEnv (rezz _) fuel)

    @0 testProp₁ : Set
    test₁ : testProp₁

    testProp₁ = testTC₁ ≡ Right _
    test₁ = refl

module TestUnifierSwap where
  open Swap
  opaque private
    basicTerm : Term α
    basicTerm = TLam "x" (TVar < inHere >)
    ℕ : Type α
    ℕ = El (STyp zero) basicTerm
    A : Type α
    A = El (STyp zero) basicTerm
    vec : Type α → Term α → Type α
    vec A _ = A

  -- (n₀ : ℕ) (v : vec A n) (m₀ : ℕ) (v' : vec A n₀) (w : vec A m₀) (w' : vec A m₀)
  Scope-n₀ = mempty ▸ "n₀"
  Scope-v = Scope-n₀ ▸ "v"
  Scope-m₀ =  Scope-v ▸ "m₀"
  Scope-v' =  Scope-m₀ ▸ "v'"
  Scope-w = Scope-v' ▸ "w"
  Scope-w' = Scope-w ▸ "w'"

  Context-n₀ = CtxEmpty , "n₀" ∶ ℕ
  Context-v : Context Scope-v
  Context-v = Context-n₀ , "v" ∶ vec A (TVar (⟨ "n₀" ⟩ inHere))
  Context-m₀ : Context Scope-m₀
  Context-m₀ = Context-v , "m₀" ∶ ℕ
  Context-v' : Context Scope-v'
  Context-v' = Context-m₀ , "v'" ∶ vec A (TVar (⟨ "n₀" ⟩ inThere (inThere inHere)))
  Context-w : Context Scope-w
  Context-w = Context-v' , "w" ∶ vec A (TVar (⟨ "m₀" ⟩ inThere inHere))
  Context-w' : Context Scope-w'
  Context-w' = Context-w , "w'" ∶  vec A (TVar (⟨ "m₀" ⟩ inThere (inThere (inHere))))

  w : NameIn Scope-w
  w = ⟨ "w" ⟩ inHere

  v' : NameIn Scope-w
  v' = ⟨ "v'" ⟩ (inThere inHere)

  m₀ : NameIn Scope-w
  m₀ = ⟨ "m₀" ⟩ (inThere (inThere inHere))

  givenfuel = Suc (Suc (Suc (Suc Zero)))
  opaque
    unfolding ScopeThings swapHighest vec

    @0 testSwapHighestBaseCaseProp : Set
    testSwapHighestBaseCase : testSwapHighestBaseCaseProp

    testSwapHighestBaseCaseProp = (swapHighest {{fl = Zero}} Context-w' w ≡ Just _ )
    testSwapHighestBaseCase = refl

    @0 testSwapHighest1Prop : Set
    testSwapHighest1 : testSwapHighest1Prop

    testSwapHighest1Prop = (swapHighest {{fl = Suc Zero}} Context-w' v' ≡ Just _ )
    testSwapHighest1 = refl

    @0 testSwapHighest2Prop : Set
    testSwapHighest2 : testSwapHighest1Prop

    testSwapHighest2Prop = (swapHighest {{fl = Suc (Suc (Suc (Suc Zero)))}} Context-w' m₀ ≡ Nothing )
    testSwapHighest2 = refl
