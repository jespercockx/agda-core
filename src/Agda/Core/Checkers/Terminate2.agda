open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.Rules.Conversion
open import Agda.Core.Rules.Typing
open import Agda.Core.TCM.Instances
open import Agda.Core.Checkers.Converter
open import Agda.Core.Rules.Terminating


module Agda.Core.Checkers.Terminate2
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private variable
  @0 x      : Name
  @0 α      : Scope Name
  @0 rβ     : RScope Name
  @0 u v    : Term α
  @0 a b c  : Type α
  @0 k l    : Sort α

private open module @0 G = Globals globals

opaque
  unfolding Scope
  iterateNthArg : (α : Scope Name) → List (NthArg α)
  iterateNthArg [] = []
  iterateNthArg (Erased x ∷ tl) = Zero x ∷ (map (Suc x) (iterateNthArg tl))
{-# COMPILE AGDA2HS iterateNthArg #-}

checkDescendingIndex : (f : FunDefinition) → (nthArg : NthArg (arity f)) → (ctx : SubTermContext α) → (prf : arity f ⊆ α) (term : Term α) → Either String (TerminatingTerm f nthArg ctx prf term)
checkDescendingIndex f nthArg ctx prf (TVar x) = Right TerminatingVar
checkDescendingIndex f nthArg ctx prf (TLam x body) = fmap TerminatingLam $ checkDescendingIndex f nthArg (StCtxExtend x Nothing ctx) (subWeaken prf) body
checkDescendingIndex f nthArg ctx prf (TDef funcName) = if (funcName == index f) 
                                                        then Left "Impossible: should have matched the App Case" 
                                                        else Right $ TerminatingDef ({!!})
checkDescendingIndex f nthArg ctx prf term = Left "Not implemented"
{-# COMPILE AGDA2HS checkDescendingIndex #-}

checkTermination : (f : FunDefinition) → Either String (Descending f)
checkTermination f = foldr helper (Left "This function is non-terminating") (iterateNthArg (arity f))
  where
    helper : NthArg (arity f) → Either String (Descending f) → Either String (Descending f)
    helper nthArg (Right res) = Right res
    helper nthArg (Left _) = 
      mapRight (DescendingIndex nthArg) 
        (checkDescendingIndex f nthArg (createStCtxFromScope StCtxEmpty (arity f)) 
          (subst0 (Sub (arity f)) (sym (leftIdentity (f .arity))) subRefl) 
          (subst0 (λ scope → Term scope) (sym (leftIdentity (f .arity))) (body f)))
{-# COMPILE AGDA2HS checkTermination #-}









