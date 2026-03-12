open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Syntax.TerminationUtils

module Agda.Core.Rules.Terminating2
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x      : Name
  @0 α β ξ  : Scope Name
  @0 rβ     : RScope Name
  @0 u v    : Term α
  @0 a b c  : Type α
  @0 k l    : Sort α

data FunDefS : @0 Scope Name → Set where
  FunDefSEmpty  : FunDefS mempty
  FunDefSExtend : (@0 def : Name)
              → FunDefinition
              → FunDefS α
              → FunDefS (α ▸ def)
{-# COMPILE AGDA2HS FunDefS deriving Show #-}

record Program : Set where
  no-eta-equality
  field
    functions : FunDefS defScope
  lookupFuncH : (fs : FunDefS α) (x : NameIn α) → FunDefinition
  lookupFuncH FunDefSEmpty x = nameInEmptyCase x
  lookupFuncH (FunDefSExtend name def rest) x = 
    nameInBindCase x
      (λ q → lookupFuncH rest (⟨ _ ⟩ q))
      (λ _ → def) 
  lookupFunc : (def : NameIn defScope) → FunDefinition
  lookupFunc = lookupFuncH functions
open Program public
{-# COMPILE AGDA2HS Program deriving Show #-}
{-# COMPILE AGDA2HS lookupFunc inline #-}

-- record FunctionCall {@0 p : Program} : Set where -- we could think about making it independent from program, by having caller and callee already be fundefinition, I am not sure
--   no-eta-equality
--   field
--     caller : NameIn defScope
--     callee : NameIn defScope
--     relations : SubTermEnv (arity (lookupFunc p callee)) -- (arity (lookupFunc p caller)) Okay this is where we modify the SubTermEnv so as to be a mapping
--     steps : List (NameIn defScope)
-- open FunctionCall public
-- {-# COMPILE AGDA2HS FunctionCall deriving Show #-}

-- record Cycle {@0 p : Program} : Set where -- we could think about making it independent from program, by having caller and callee already be fundefinition, I am not sure
--   no-eta-equality
--   field
--     function : NameIn defScope
--     relations : SubTermEnv (arity (lookupFunc p function)) -- (arity (lookupFunc p function)) Okay this is where we modify the SubTermEnv so as to be a mapping
--     steps : List (NameIn defScope) -- not really needed anymore, although might be useful to distinguish between cycles?
-- open Cycle public
-- {-# COMPILE AGDA2HS Cycle deriving Show #-}


data FragmentTerm : @0 Term α → @0 Term β → Set -- Maybe explore relation between alpha and beta?
data FragmentTerm where
  FragmentLam :
    {@0 term : Term α}
    {@0 body : Term (bind α x)}
    {@0 name : Name}
    → @0 term ≡ TLam x body
    → FragmentTerm body term
  FragmentAppBody :
    {@0 term : Term α}
    {@0 body : Term α}
    {@0 arg : Term α}
    {@0 name : Name}
    → @0 term ≡ TApp body arg
    → FragmentTerm body term
  FragmentAppArg :
    {@0 term : Term α}
    {@0 body : Term α}
    {@0 arg : Term α}
    {@0 name : Name}
    → @0 term ≡ TApp body arg
    → FragmentTerm arg term
  FragmentLetBody :
    {@0 term : Term α}
    {@0 body : Term α}
    {@0 cont : Term (bind α x)}
    {@0 name : Name}
    → @0 term ≡ TLet x body cont
    → FragmentTerm body term
  FragmentLetCont :
    {@0 term : Term α}
    {@0 body : Term α}
    {@0 cont : Term (bind α x)}
    {@0 name : Name}
    → @0 term ≡ TLet x body cont
    → FragmentTerm cont term
  FragmentTrans :
    {@0 term1 : Term α}
    {@0 term2 : Term β}
    {@0 term3 : Term ξ}
    → FragmentTerm term1 term2
    → FragmentTerm term2 term3
    → FragmentTerm term1 term3
    
