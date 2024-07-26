module Agda.Core.TestTypeCheck where

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

{-# TERMINATING #-}
fuel : Fuel
fuel = More fuel

natfuel : Nat → Fuel
natfuel zero = None
natfuel (suc n) = More (natfuel n)

opaque
  unfolding ScopeThings

  `true : Term α
  `true = TCon "true" (inHere) SNil
  `false : Term α
  `false = TCon "false" (inThere inHere) SNil

opaque
  unfolding All Sub Split inHere inThere lookupAll
  unfolding subLeft splitRefl subBindDrop subJoinDrop splitJoinRight

  trueCon : Constructor ∅ "true" inHere
  trueCon = record { conTelescope = EmptyTel }

  falseCon : Constructor ∅ "false" (inThere inHere)
  falseCon = record { conTelescope = EmptyTel }

  boolDef : Datatype
  boolDef = record
    { dataPars = ∅
    ; dataCons = cons
    ; dataSort = STyp 0
    ; dataParTel = EmptyTel
    ; dataConstructors =
       allJoin (allSingl (inHere Σ,
                          trueCon))
      (allJoin (allSingl (inThere inHere Σ,
                          falseCon ))
               allEmpty)
    }

  sig : Signature
  sig = allSingl (El (STyp 1) (TSort (STyp 0)), DatatypeDef (boolDef))

open import Agda.Core.Context globals
open import Agda.Core.TCM globals sig
open import Agda.Core.TCMInstances
open import Agda.Core.Typing globals sig
open import Agda.Core.Typechecker globals sig

{-
Agda.Core.Syntax.Subst globals
      (lookupAll
       (allJoin (allSingl Scope.Core.scopeMempty)
        (allJoin (allSingl Scope.Core.scopeMempty) allEmpty))
       inHere)
      Scope.Core.scopeMempty
-}

trueType : Type ∅
trueType = constructorType "Bool" subRefl "true" inHere trueCon (STyp 0) SNil (subst0 (λ p → p ⇒ ∅) (sym $ lookupHere _ ∅) SNil) 

it : TCM (Σ[ t ∈ Type ∅ ] CtxEmpty ⊢ `true ∶ t)
it = inferType CtxEmpty `true

ct : TCM (CtxEmpty ⊢ `true ∶ trueType )
ct = checkType CtxEmpty `true trueType

tcmenv : TCEnv
tcmenv = MkTCEnv (rezz sig) (natfuel 100)

isRight : Either TCError b -> String
isRight (Left x) = "Error: " ++ show x
isRight (Right x) = "Typechecked!"

r : String
r = isRight (runTCM ct tcmenv)

