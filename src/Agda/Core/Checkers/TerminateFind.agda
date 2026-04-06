open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Syntax.TerminationUtils
open import Agda.Core.Rules.Terminating
open import Agda.Core.Checkers.Terminate
open import Agda.Core.Reduce
open import Agda.Core.Rules.Conversion
open import Agda.Core.Rules.Typing
open import Agda.Core.TCM.Instances
open import Agda.Core.Checkers.Converter


module Agda.Core.Checkers.TerminateFind
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x : Name
  @0 α β : Scope Name
  @0 rβ : RScope Name

checkSubtermVar : SubTermEnv β α → NameIn β → NameIn α → Bool
checkSubtermVar ctx (⟨ _ ⟩ ( param ⟨ _ ⟩)) arg = case (lookupSt ctx arg) of λ where
  (Decreasing (⟨ _ ⟩ ( parent ⟨ _ ⟩))) → case (param == parent) of λ where
    True → True
    False → False -- this needs eventually to check recursively
  _ → False
{-# COMPILE AGDA2HS checkSubtermVar #-}

checkSubterm : SubTermEnv β α → NameIn β → Term α → Bool
checkSubterm con param (TVar arg) = checkSubtermVar con param arg
checkSubterm con name term = False
{-# COMPILE AGDA2HS checkSubterm #-}


-- At some point make the lists vecs for more security
compareArgsToParams : SubTermEnv β α → List (NameIn β) → List (Term α) → List Bool
compareArgsToParams con (param ∷ params) (arg ∷ args) = checkSubterm con param arg ∷ compareArgsToParams con params args
compareArgsToParams _ _ _ = []
{-# COMPILE AGDA2HS compareArgsToParams #-}

{-# NON_TERMINATING #-} -- need to find a way to not need those
handleBranches : ∀ {@0 d : NameData} {@0 cs : RScope (NameCon d)} → SubTermEnv β α → NameIn defScope → List (NameIn β) → Relation β → (bs : Branches α d cs) → List Bool

getDecreasingArgs : SubTermEnv β α → NameIn defScope → List (NameIn β) → Term α → List Bool

handleBranches con funName params rel BsNil = map (λ _ → True) params
handleBranches {α} {β} con funName params rel (BsCons (BBranch (c ⟨ w ⟩ ) (fields ⟨ p ⟩ ) clause) branches) = 
  zipWith (λ x y → x && y)
  (getDecreasingArgs (updateEnv con fields rel) funName
    params
    (subst0 (λ f → Term (β ◂▸ f)) p clause))
  (handleBranches con funName params rel branches)

{-# COMPILE AGDA2HS handleBranches #-}


getDecreasingArgs con funName params (TApp u v) =  case unApps (TApp u v) of λ where
  (fun , args) → zipWith (λ x y → x && y) (foldr (zipWith (λ x y → x && y)) (map (λ _ → True) params) (map (getDecreasingArgs con funName params) args)) (case fun of λ where
    (TDef d) → case (d == funName) of λ where
     True → compareArgsToParams con params args
     False → map (λ _ → True) params
    x → getDecreasingArgs con funName params x)
getDecreasingArgs con funName params (TLam name body) = 
  getDecreasingArgs (StEnvExtend name Unrelated con) funName params body
getDecreasingArgs con funName params (TLet name body1 body2) = 
  zipWith (λ x y → x && y) (getDecreasingArgs con funName params body1) 
    (getDecreasingArgs (StEnvExtend name Unrelated con) funName params body2)
getDecreasingArgs con funName params (TCase _ _ (TVar nameVar) branches _) = -- we only accept pattern matching on variable for now.
  handleBranches con funName params (descend $ lookupSt con nameVar) branches
getDecreasingArgs _ _ params _ = map (λ _ → True) params
{-# COMPILE AGDA2HS getDecreasingArgs #-}

opaque
  unfolding Scope
  createNthArgFromDecArgs : {α : Scope Name} → List Bool → Maybe (NthArg α)
  createNthArgFromDecArgs {[]} [] = Nothing
  createNthArgFromDecArgs {Erased x ∷ restScope} (False ∷ rest) = case createNthArgFromDecArgs rest of λ where
    Nothing → Nothing
    (Just nthArg) → Just $ SucNA x nthArg
  createNthArgFromDecArgs {Erased x ∷ restScope} (True ∷ rest) = Just $ ZeroNA x
  createNthArgFromDecArgs _ = Nothing -- impossible
{-# COMPILE AGDA2HS createNthArgFromDecArgs #-}

checkTerminationFind' : (f : FunDefinition) → List (NameIn (arity f)) → Either String (Descending f)
checkTerminationFind' f params = do
  catchEither
    (
      do
        descBodyNoNothArg ← checkDescendingIndex f Nothing (createStEnvFromScope (arity f)) (body f)
        Right $ DescendingIndex Nothing descBodyNoNothArg
    )
    (λ _ → 
      (case (createNthArgFromDecArgs {arity f} (reverse $ getDecreasingArgs (createStEnvFromScope (arity f)) (index f) params (body f))) of λ where
        Nothing → Left "No arg was found to be terminating"
        (Just nthArg) → do
          descBody <- (checkDescendingIndex f (Just nthArg) (createStEnvFromScope (arity f)) 
                        (body f))
          Right $ DescendingIndex (Just nthArg) descBody))
{-# COMPILE AGDA2HS checkTerminationFind' #-}

checkTerminationFind : {α : Scope Name} → List (NameIn α) → NameIn defScope → Term α → Either String String
checkTerminationFind params def (TLam x body) = checkTerminationFind ((map (weakenNameIn (subWeaken subRefl)) params) ++ ((⟨ x ⟩ Zero ⟨ IsZero refl ⟩) ∷ [])) def body
checkTerminationFind {α} params def body = do
  DescendingIndex r i ← checkTerminationFind' (record { index = def; arity = α; body = body }) params
  Right ("The function is terminating in its " ++ show r)
{-# COMPILE AGDA2HS checkTerminationFind #-}
-- (record { index = def; arity = α; body = body })
