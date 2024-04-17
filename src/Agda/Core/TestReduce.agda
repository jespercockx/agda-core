{-# OPTIONS --overlapping-instances #-}

module Agda.Core.TestReduce where

open import Haskell.Prelude hiding (All)

open import Haskell.Extra.Erase
open import Haskell.Law.Equality
open import Haskell.Extra.Refinement

open import Scope
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Utils renaming ( _,_ to _Σ,_)

name = String

private variable
  x y : name
  α : Scope name

instance
  top : In x (x ◃ α)
  top = inHere

  pop : {{x ∈ α}} → x ∈ (y ◃ α)
  pop {{p}} = inThere p

defs = singleton "Bool"

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

boolcons : All (λ c → Σ (c ∈ cons) (Constructor mempty mempty c)) cons
boolcons = allJoin (allSingl (inHere
                             Σ, record { conTelescope =
                                          subst0 (λ x → Telescope mempty x)
                                                 (sym $ lookupHere _ _)
                                                 EmptyTel
                                      ; conIndices = SNil } )) $
           allJoin (allSingl (inThere inHere
                             Σ, record { conTelescope =
                                          subst0 (λ x → Telescope mempty x)
                                                 (sym $ lookupThere (lookupHere _ _))
                                                 EmptyTel
                                      ; conIndices = SNil })) $
           allEmpty

bool : Datatype
bool .dataParameterScope = mempty
bool .dataIndexScope = mempty
bool .dataConstructorScope = cons
bool .dataSort = STyp 0
bool .dataParameterTel = EmptyTel
bool .dataIndexTel = EmptyTel
bool .dataConstructors = boolcons

sig : Signature
sig = allSingl ((El (STyp 1) (TSort $ dataSort bool)) , DatatypeDef bool)

open import Agda.Core.Reduce globals

{-# TERMINATING #-}
fuel : Fuel
fuel = More fuel

opaque
  unfolding ScopeThings

  `true : Term α
  `true = TCon "true" (inHere) SNil
  `false : Term α
  `false = TCon "false" (inThere inHere) SNil

module Tests (@0 x y z : name) where

  opaque
    unfolding ScopeThings `true `false

    testTerm₁ : Term α
    testTerm₁ = apply (TLam x (TVar x inHere)) (TSort (STyp 0))

    @0 testProp₁ : Set
    testProp₁ = reduceClosed sig testTerm₁ fuel ≡ Just (TSort (STyp 0))

    test₁ : testProp₁
    test₁ = refl

    testTerm₂ : Term α
    testTerm₂ = TApp `true (ECase {x = "condition"}
                                  (BsCons (BBranch "true" inHere (rezz _) `false) 
                                  (BsCons (BBranch "false" (inThere inHere) (rezz _) `true)
                                   BsNil))
                                  (El (STyp 0) (TDef "Bool" inHere)))

    @0 testProp₂ : Set
    testProp₂ = reduceClosed sig testTerm₂ fuel ≡ Just `false

    test₂ : testProp₂
    test₂ = refl

-- -}
