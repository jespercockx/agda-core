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

defs = bind "Bool" $ bind "Unit" mempty

cons = bind "true" $ bind "false" $ bind "unit" mempty

conArity : All (λ _ → Scope name) cons
conArity = allJoin (allSingl mempty)
          (allJoin (allSingl mempty)
          (allJoin (allSingl mempty)
          allEmpty))

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
  `unit : Term α
  `unit = TCon "unit" (inThere $ inThere inHere) SNil

opaque
  unfolding All Sub Split inHere inThere lookupAll
  unfolding subLeft splitRefl subBindDrop subJoinDrop splitJoinRight

  trueCon : Constructor ∅ "true" inHere
  trueCon = record { conTelescope = EmptyTel }

  falseCon : Constructor ∅ "false" (inThere inHere)
  falseCon = record { conTelescope = EmptyTel }

  unitCon : Constructor ∅ "unit" (inThere $ inThere $ inHere)
  unitCon = record { conTelescope = EmptyTel }

boolCons : Scope name
boolCons = bind "true" $ bind "false" mempty
  
boolDef : Datatype
boolDef = record
  { dataPars = ∅
  ; dataCons = boolCons
  ; dataSort = STyp 0
  ; dataParTel = EmptyTel
  ; dataConstructors =
     allJoin (allSingl (inHere Σ,
                        trueCon))
    (allJoin (allSingl (inThere inHere Σ,
                        falseCon ))
             allEmpty)
  }

unitDef : Datatype
unitDef = record
  { dataPars = ∅
  ; dataCons = singleton "unit"
  ; dataSort = STyp 0
  ; dataParTel = EmptyTel
  ; dataConstructors = allSingl (inThere (inThere inHere) Σ, unitCon)
  }

sig : Signature
sig =
  allJoin
    (allSingl (El (STyp 1) (TSort (STyp 0)), DatatypeDef (boolDef))) $
  allJoin
    (allSingl ((El (STyp 1) (TSort (STyp 0))) , (DatatypeDef unitDef)))
  allEmpty
                

open import Agda.Core.Context globals
open import Agda.Core.TCM globals sig
open import Agda.Core.TCMInstances
open import Agda.Core.Typing globals sig
open import Agda.Core.Typechecker globals sig

tcmenv : TCEnv
tcmenv = MkTCEnv (rezz sig) (natfuel 100)

isRight : Either TCError b -> String
isRight (Left x) = "Error: " ++ show x
isRight (Right x) = "Typechecked!"

typecheck : Context α → Term α → Type α → String
typecheck ctx term type = isRight (runTCM (checkType ctx term type) tcmenv)

typeinfer : Context α → Term α → String
typeinfer ctx term = isRight (runTCM (inferType ctx term) tcmenv)

trueType : Type ∅
trueType = constructorType "Bool" inHere "true" inHere trueCon (STyp 0) SNil (subst0 (λ p → p ⇒ ∅) (sym $ lookupHere _ ∅) SNil)

unitType : Type ∅
unitType = constructorType "Unit" (inThere inHere) "unit" (inThere $ inThere inHere) unitCon (STyp 0) SNil (subst0 (λ p → p ⇒ ∅) (sym $ lookupThere $ lookupThere $ lookupHere _ ∅) SNil)

r : String
r = typecheck CtxEmpty `true trueType

if-then-else : Term α → Term α → Term α → Type (x ◃ α) → Term α
if-then-else c t e ty =
  TApp c (ECase
    (BsCons (BBranch "true" inHere            (rezz _)
               (weaken (subJoinDrop (rezz _) subRefl) t)) $
     BsCons (BBranch "false" (inThere inHere) (rezz _)
               (weaken (subJoinDrop (rezz _) subRefl) t))
     BsNil)
    ty)

type : Type ∅
type = El (STyp 1)
          (TPi "x"
            (trueType)
            (El (STyp 0)
                (if-then-else {x = "xs"} (TVar "x" inHere)
                              (weaken subEmpty (unType trueType))
                              (weaken subEmpty (unType unitType))
                              (weakenType subEmpty (El (STyp 1) (TSort (STyp 0)))))))

body : Term ∅
body = TLam "x" $
  if-then-else {x = "xs"} (TVar "x" inHere) `true `unit $
               El (STyp 0) $ if-then-else {x = "xs"} (TVar _ inHere)
                                          (weaken subEmpty (unType trueType))
                                          (weaken subEmpty (unType unitType))
                                          (El (STyp 1) (TSort (STyp 0)))

test : typecheck CtxEmpty body type ≡ "Typechecked!"
test = {!refl!}
