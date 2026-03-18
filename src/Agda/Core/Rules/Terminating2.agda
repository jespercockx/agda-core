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

record FunctionCall (@0 p : Program) : Set where -- we could think about making it independent from program, by having caller and callee already be fundefinition, I am not sure
  no-eta-equality
  field
    caller : NameIn defScope
    callee : NameIn defScope
    relations : SubTermEnv (arity (lookupFunc p callee)) (arity (lookupFunc p caller)) --  Okay this is where we modify the SubTermEnv so as to be a mapping
open FunctionCall public
{-# COMPILE AGDA2HS FunctionCall deriving Show #-}

data CallChain (@0 p : Program) : @0 NameIn defScope → @0 NameIn defScope → Set where
  ChainNil  : (fc : FunctionCall p)
            → CallChain p (caller fc) (callee fc)
  ChainCons : {@0 end : NameIn defScope}
            → (fc : FunctionCall p)
            → CallChain p (callee fc) end
            → CallChain p (caller fc) end
{-# COMPILE AGDA2HS CallChain deriving Show #-}

record Cycle (@0 p : Program) : Set where
  no-eta-equality
  constructor MkCycle
  field
    @0 {func} : NameIn defScope
    chain : CallChain p func func
open Cycle public
{-# COMPILE AGDA2HS Cycle deriving Show #-}

data CycleS (@0 p : Program) : Set where
  CycleSNil : CycleS p
  CycleSCons : Cycle p → CycleS p → CycleS p
{-# COMPILE AGDA2HS CycleS deriving Show #-}

bindRelation : {@0 α β : Scope Name} → Relation α → (NameIn α → Relation β) → Relation β
bindRelation Unrelated       _ = Unrelated
bindRelation (NonIncreasing n) f = f n
bindRelation (Decreasing    n) f =
  case f n of λ where
    Unrelated       → Unrelated
    (NonIncreasing m) → Decreasing m
    (Decreasing    m) → Decreasing m

computeTransitiveRelations : SubTermEnv α β → SubTermEnv β ξ → SubTermEnv α ξ
computeTransitiveRelations env StEnvEmpty = StEnvEmpty
computeTransitiveRelations env (StEnvExtend name rel rest) = StEnvExtend name (bindRelation rel (lookupSt env)) (computeTransitiveRelations env rest)

computeChainsRelations : {p : Program} {caller callee : NameIn defScope} → CallChain p caller callee → SubTermEnv (arity (lookupFunc p callee)) (arity (lookupFunc p caller))
computeChainsRelations (ChainNil fc) = relations fc
computeChainsRelations (ChainCons fc chain) = computeTransitiveRelations (computeChainsRelations chain) (relations fc)

data DescendingRecursiveCallHelper : @0 SubTermEnv α β → @0 β ⊆ α → Set where
  DescendingRecursiveCallMatch : 
    {@0 nameIn : NameIn α}
    {env : SubTermEnv α β}
    (let ⟨ name ⟩ p = nameIn)
    {prf : bind β name ⊆ α}
    → DescendingRecursiveCallHelper (StEnvExtend name (Decreasing (nameIn)) env) prf
  DescendingRecursiveCallExtend : 
    {env : SubTermEnv α β}
    {name : Name}
    {prf : Sub (bind β name) α}
    {rel : Relation α}
    → DescendingRecursiveCallHelper env (subWeaken' prf)
    → DescendingRecursiveCallHelper (StEnvExtend name rel env) prf
{-# COMPILE AGDA2HS DescendingRecursiveCallHelper deriving Show #-}

record DescendingRecursiveCall (@0 env : SubTermEnv α α) : Set
record DescendingRecursiveCall env where
  no-eta-equality
  field
    descendingParameterHelper : DescendingRecursiveCallHelper env subRefl
open DescendingRecursiveCall public
{-# COMPILE AGDA2HS DescendingRecursiveCall deriving Show #-}
  
record TerminatingCycle (@0 p : Program) (@0 c : Cycle p) : Set where
  no-eta-equality
  field
    descendingParameter : DescendingRecursiveCall (computeChainsRelations (chain c))
open TerminatingCycle public
{-# COMPILE AGDA2HS TerminatingCycle deriving Show #-}

data TerminatingCycleS (@0 p : Program) : @0 CycleS p → Set where
  TerminatingCycleSNil : TerminatingCycleS p CycleSNil
  TerminatingCycleSCons : {cycle : Cycle p}
                          {cycles : CycleS p}
                          → TerminatingCycle p cycle
                          → TerminatingCycleS p cycles
                          → TerminatingCycleS p (CycleSCons cycle cycles)
{-# COMPILE AGDA2HS TerminatingCycleS deriving Show #-}

record Terminating (@0 p : Program) : Set where
  no-eta-equality
  field
    @0 allCycles : (c : Cycle p) → TerminatingCycle p c
open Terminating public
{-# COMPILE AGDA2HS Terminating deriving Show #-}
