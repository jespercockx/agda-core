{-# OPTIONS --overlapping-instances #-}

module Agda.Core.TestReduce where

open import Haskell.Prelude hiding (All)

open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement

open import Scope
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Utils

name = String

private variable
  x y : name
  α : Scope name

instance
  top : In x (x ◃ α)
  top = inHere

  pop : {{x ∈ α}} → x ∈ (y ◃ α)
  pop {{p}} = inThere p

defs = mempty

cons = bind "true" $ bind "false" mempty

conArity : All (λ _ → Scope name) cons
conArity = allJoin (allSingl mempty) (allJoin (allSingl mempty) allEmpty)

globals : Globals name
globals = record 
  { defScope = defs
  ; conScope = cons
  ; fieldScope = conArity
  }


open import Agda.Core.Syntax globals
open import Agda.Core.Signature globals

sig : Signature
sig = allEmpty

open import Agda.Core.Reduce globals

opaque
  unfolding lookupAll inHere inThere splitRefl splitJoinRight subBindDrop subLeft

  `true : Term α
  `true = TCon "true" (inHere) SNil
  `false : Term α
  `false = TCon "false" (inThere inHere) SNil

{-# TERMINATING #-}
fuel : Fuel
fuel = More fuel

module Tests (@0 x y z : name) where

  opaque
    unfolding step inBindCase inSplitCase inJoinCase `true `false decIn ∅-⋈-injective

    testTerm₁ : Term α
    testTerm₁ = apply (TLam x (TVar x inHere)) (TSort (STyp 0))

    @0 testProp₁ : Set
    testProp₁ = reduceClosed sig testTerm₁ fuel ≡ Just (TSort (STyp 0))

    test₁ : testProp₁
    test₁ = refl

    testTerm₂ : Term α
    testTerm₂ = TApp `true (ECase (BsCons (BBranch "true" inHere (rezz _) `false) 
                                  (BsCons (BBranch "false" (inThere inHere) (rezz _) `true)
                                   BsNil)))

    @0 testProp₂ : Set
    testProp₂ = reduceClosed sig testTerm₂ fuel ≡ Just `false

    test₂ : testProp₂
    test₂ = refl

-- -}
