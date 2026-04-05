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
{-# COMPILE AGDA2HS FunDefS #-}

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
{-# COMPILE AGDA2HS Program #-}
{-# COMPILE AGDA2HS lookupFunc inline #-}

record FunctionCall (@0 p : Program) : Set where -- we could think about making it independent from program, by having caller and callee already be fundefinition, I am not sure
  no-eta-equality
  field
    caller : NameIn defScope
    callee : NameIn defScope
    relations : SubTermEnv (arity (lookupFunc p callee)) (arity (lookupFunc p caller)) --  Okay this is where we modify the SubTermEnv so as to be a mapping
open FunctionCall public
{-# COMPILE AGDA2HS FunctionCall #-}

record Graph (@0 p : Program) : Set where
  no-eta-equality
  field
    functionCalls : List (FunctionCall p)
open Graph public
{-# COMPILE AGDA2HS Graph #-}

data CallChain {@0 p : Program} (@0 g : Graph p) : @0 NameIn defScope → @0 NameIn defScope → Set where
  ChainSing  : (fc : FunctionCall p)
            → @0 ListIn (λ x → x .caller == fc .caller && x .callee == fc .callee) (g .functionCalls) -- here later change condition to also include env equality
            → CallChain g (caller fc) (callee fc)
  ChainCons : {@0 end : NameIn defScope}
            → (fc : FunctionCall p)
            → @0 ListIn (λ x → x .caller == fc .caller && x .callee == fc .callee) (g .functionCalls) -- here later change condition to also include env equality
            → CallChain g (callee fc) end
            → CallChain g (caller fc) end
{-# COMPILE AGDA2HS CallChain #-}

record Cycle (@0 p : Program) (@0 g : Graph p) : Set where
  no-eta-equality
  constructor MkCycle
  field
    @0 {func} : NameIn defScope
    chain : CallChain g func func
open Cycle public
{-# COMPILE AGDA2HS Cycle #-}

data CycleS (@0 p : Program) (@0 g : Graph p) : Set where
  CycleSNil : CycleS p g
  CycleSCons : Cycle p g → CycleS p g → CycleS p g
{-# COMPILE AGDA2HS CycleS #-}

bindRelation : {@0 α β : Scope Name} → Relation α → (NameIn α → Relation β) → Relation β
bindRelation Unrelated       _ = Unrelated
bindRelation (NonIncreasing n) f = f n
bindRelation (Decreasing    n) f =
  case f n of λ where
    Unrelated         → Unrelated
    (NonIncreasing m) → Decreasing m
    (Decreasing    m) → Decreasing m

computeTransitiveRelations : SubTermEnv α β → SubTermEnv β ξ → SubTermEnv α ξ
computeTransitiveRelations env StEnvEmpty = StEnvEmpty
computeTransitiveRelations env (StEnvExtend name rel rest) = StEnvExtend name (bindRelation rel (lookupSt env)) (computeTransitiveRelations env rest)

computeChainsRelations : {p : Program} {g : Graph p} {caller callee : NameIn defScope} → CallChain g caller callee → SubTermEnv (arity (lookupFunc p callee)) (arity (lookupFunc p caller))
computeChainsRelations (ChainSing fc _) = relations fc
computeChainsRelations (ChainCons fc _ chain) = computeTransitiveRelations (computeChainsRelations chain) (relations fc)

data DescendingRecursiveCall : @0 SubTermEnv α β → @0 β ⊆ α → Set where
  DescendingRecursiveCallMatch : 
    {@0 nameIn : NameIn α}
    {env : SubTermEnv α β}
    (let ⟨ name ⟩ p = nameIn)
    {prf : bind β name ⊆ α}
    → DescendingRecursiveCall (StEnvExtend name (Decreasing nameIn) env) prf
  DescendingRecursiveCallExtend : 
    {env : SubTermEnv α β}
    {name : Name}
    {prf : (bind β name) ⊆ α}
    {rel : Relation α}
    → DescendingRecursiveCall env (subWeaken' prf)
    → DescendingRecursiveCall (StEnvExtend name rel env) prf
{-# COMPILE AGDA2HS DescendingRecursiveCall #-}

record TerminatingCycle {@0 p : Program} (@0 g : Graph p) (@0 c : Cycle p g) : Set where
  no-eta-equality
  field
    descendingParameter : DescendingRecursiveCall (computeChainsRelations (chain c)) subRefl
open TerminatingCycle public
{-# COMPILE AGDA2HS TerminatingCycle #-}

data TerminatingCycleS {@0 p : Program} (@0 g : Graph p) : @0 CycleS p g → Set where
  TerminatingCycleSNil : TerminatingCycleS g CycleSNil
  TerminatingCycleSCons : {cycle : Cycle p g}
                          {cycles : CycleS p g}
                          → TerminatingCycle g cycle
                          → TerminatingCycleS g cycles
                          → TerminatingCycleS g (CycleSCons cycle cycles)
{-# COMPILE AGDA2HS TerminatingCycleS #-}

data GraphTermS {@0 p : Program} (@0 g : Graph p) (@0 f : FunDefinition) (@0 env : SubTermEnv (arity f) α) : @0 (TermS α rβ) → Set
data GraphTerm {@0 p : Program} (@0 g : Graph p) (@0 f : FunDefinition) (@0 env : SubTermEnv (arity f) α) : Term α → Set
data GraphBranches {@0 p : Program} (@0 g : Graph p) {@0 d : NameData} (@0 f : FunDefinition) (@0 env : SubTermEnv (arity f) α) (@0 patternMatchedVariable : NameIn α) (@0 rel : Relation (arity f)) : {@0 cs : RScope (NameCon d)} → (@0 bs : Branches α d cs) → Set
data GraphBranch {@0 p : Program} (@0 g : Graph p) {@0 d : NameData} (@0 f : FunDefinition) (@0 env : SubTermEnv (arity f) α) (@0 patternMatchedVariable : NameIn α) (@0 rel : Relation (arity f)) : {@0 c : NameCon d} → @0 Branch α c → Set
data GraphBranches {α = α} g {d = d} f env var rel where
  GraphNil : GraphBranches g f env var rel BsNil
  GraphCons : ∀ {@0 c : NameCon d} {@0 cs : RScope (NameCon d)} {@0 b : Branch α c} {@0 bs : Branches α d cs}
           → GraphBranch g f env var rel b
           → GraphBranches g f env var rel bs
           → GraphBranches g f env var rel (BsCons b bs)
{-# COMPILE AGDA2HS GraphBranches #-}

data GraphTerm {α} g f env where
  GraphVar :
    {x : NameIn α}
    --------------------------------------------------------------
    → GraphTerm g f env (TVar x)

  GraphCon :
    {d : NameData}
    {c : NameCon d}
    {@0 us  : TermS α (fieldScope c)}
    → GraphTermS g f env us
    --------------------------------------------------------------
    → GraphTerm g f env (TCon c us)

  GraphData :
    {d : NameData}
    {@0 pars : TermS α (dataParScope d)}
    {@0 ixs  : TermS α (dataIxScope  d)}
    ----------------------------------------------
    → GraphTermS g f env pars
    → GraphTermS g f env ixs
    → GraphTerm g f env (TData d pars ixs)

  GraphLam :
    {@0 body : Term (bind α x)}
    → GraphTerm g f (StEnvExtend x Unrelated env) body 
    --------------------------------------------------------------
    → GraphTerm g f env (TLam x body)

  GraphLet :
    {@0 body : Term α}
    {@0 rest : Term (bind α x)}
    → GraphTerm g f env body 
    → GraphTerm g f (StEnvExtend x Unrelated env) rest 
    --------------------------------------------------------------
    → GraphTerm g f env (TLet x body rest)

  GraphCase :
    {d : NameData}                                                -- the name of a datatype
    {@0 varName : NameIn α}                                       -- name of the variable we are pattern matching on (this only supports cases on variables)
    (let iScope = dataIxScope d                                   -- indexes of d
         α'     = α ◂▸ iScope                                     -- general scope + indexes
         iRun   = sing iScope)                                    -- runtime index scope
    {cases : Branches α d (AllNameCon d)}                         -- cases for constructors of dt
    {return : Type (α' ▸ x)}                                      -- return type

    → GraphBranches g f env varName (descend $ lookupSt env varName) cases          -- Proof that each branch is terminating

    --------------------------------------------------
    → GraphTerm g f env (TCase d iRun (TVar varName) cases return)


data GraphBranch {α = α}  g {d = d} f env var rel where
  GraphBBranch :
              {@0 c : NameCon d}
              {rhs : Term (α ◂▸ (fieldScope c))}
            → GraphTerm g f (updateEnv env (fieldScope c) rel ) rhs
            → GraphBranch g f env var rel (BBranch (sing c) ((fieldScope c) ⟨ refl ⟩) rhs)
{-# COMPILE AGDA2HS GraphBranch #-}

data GraphTermS {α} g f env where
  GraphTermSNil : GraphTermS g f env TSNil
  TerminatingTermSCons : 
    {@0 term : Term α}
    {@0 name : Name}
    {@0 terml : (TermS α rβ)}
    → GraphTerm g f env term
    → GraphTermS g f env terml
    → GraphTermS g f env (TSCons {x = name} term terml)
{-# COMPILE AGDA2HS GraphTermS #-}

data GraphCoversCalls {@0 p : Program} (@0 g : Graph p) : FunDefS α → Set where
  GraphCoversCallsNil :
    GraphCoversCalls g FunDefSEmpty
  GraphCoversCallsCons :
    {defName : Name}
    {def : FunDefinition}
    {fds : FunDefS α}
    -- here add the actual check
    → GraphTerm g def (createStEnvFromScope (arity def)) (body def)
    → GraphCoversCalls g (FunDefSExtend defName def fds)

record Terminating (@0 p : Program) (@0 g : Graph p) : Set where
  no-eta-equality
  field
    @0 allCycles : (c : Cycle p g) → TerminatingCycle g c -- all cycles are terminating
    @0 graphCoversCalls : GraphCoversCalls g (functions p) -- the graph/certificate covers all recursive calls in the program
open Terminating public
{-# COMPILE AGDA2HS Terminating #-}
