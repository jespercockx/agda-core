open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Syntax.TerminationUtils

module Agda.Core.Rules.Terminating
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x      : Name
  @0 α β    : Scope Name
  @0 rβ     : RScope Name
  @0 u v    : Term α
  @0 a b c  : Type α
  @0 k l    : Sort α


data TerminatingTermList (@0 f : FunDefinition) (@0 nthArg : Maybe (NthArg (arity f))) (@0 env : SubTermEnv (arity f) α) : @0 List (Term α) → Set
data TerminatingTermS (@0 f : FunDefinition) (@0 nthArg : Maybe (NthArg (arity f))) (@0 env : SubTermEnv (arity f) α) : @0 (TermS α rβ) → Set

data TerminatingBranches {@0 d : NameData} (@0 f : FunDefinition) (@0 nthArg : Maybe (NthArg (arity f))) (@0 env : SubTermEnv (arity f) α) (@0 patternMatchedVariable : NameIn α) (@0 rel : Relation (arity f)) : {@0 cs : RScope (NameCon d)} → (@0 bs : Branches α d cs) → Set
data TerminatingTerm (@0 f : FunDefinition) (@0 nthArg : Maybe (NthArg (arity f))) (@0 env : SubTermEnv (arity f) α) : @0 Term α → Set
data TerminatingBranch {@0 d : NameData} (@0 f : FunDefinition) (@0 nthArg : Maybe (NthArg (arity f))) (@0 env : SubTermEnv (arity f) α) (@0 patternMatchedVariable : NameIn α) (@0 rel : Relation (arity f)) : {@0 c : NameCon d} → @0 Branch α c → Set

-- certificate that a term is always decreasing in the given parameter for function f
data TerminatingTerm {α} f nthArg env where

  TerminatingVar :
    {x : NameIn α}
    --------------------------------------------------------------
    → TerminatingTerm f nthArg env (TVar x)

  TerminatingCon :
    {d : NameData}
    {c : NameCon d}
    {@0 us  : TermS α (fieldScope c)}
    → TerminatingTermS f nthArg env us
    --------------------------------------------------------------
    → TerminatingTerm f nthArg env (TCon c us)

  TerminatingData :
    {d : NameData}
    {@0 pars : TermS α (dataParScope d)}
    {@0 ixs  : TermS α (dataIxScope  d)}
    ----------------------------------------------
    → TerminatingTermS f nthArg env pars
    → TerminatingTermS f nthArg env ixs
    → TerminatingTerm f nthArg env (TData d pars ixs)

  TerminatingApp :
    {@0 function : Term α}
    {@0 argument : Term α}
    → TerminatingTerm f nthArg env function 
    → TerminatingTerm f nthArg env argument 
    --------------------------------------------------------------
    → TerminatingTerm f nthArg env (TApp function argument)

  DecreasingNthArgApp :
    {@0 function : Term α}
    {@0 x : NameIn α} -- The argument is a variable (TVar)
    {@0 realNthArg : NthArg (arity f)}
    (let (func , args) = unApps function)

    → @0 nthArg ≡ (Just realNthArg)
    → @0 func ≡ TDef (index f)
    → @0 (lengthN args) ≡ indexOf (lengthScope (arity f)) realNthArg -- The number of arguments to the left of that application corresponds to the index of the decreasing parameter
    → @0 lookupSt env x ≡ Decreasing (getNthArg realNthArg) -- The argument corresponding to the decreasing parameter is indeed a subterm of said parameter
    → TerminatingTermList f nthArg env args
    --------------------------------------------------------------
    → TerminatingTerm f nthArg env (TApp function (TVar x))

  -- We can use this because we assume all functions defined up to that point have been termination checked themselves, which itself assumes corecursion is not handled, which it isn't yet.
  TerminatingDef :
    {@0 functionName : NameIn defScope}
    → @0 Not (functionName ≡ index f)
    --------------------------------------------------------------
    → TerminatingTerm f nthArg env (TDef functionName)

  TerminatingLam :
    {@0 body : Term (bind α x)}
    → TerminatingTerm f nthArg (StEnvExtend x Unrelated env) body 
    --------------------------------------------------------------
    → TerminatingTerm f nthArg env (TLam x body)

  TerminatingLet :
    {@0 body : Term α}
    {@0 rest : Term (bind α x)}
    → TerminatingTerm f nthArg env body 
    → TerminatingTerm f nthArg (StEnvExtend x Unrelated env) rest 
    --------------------------------------------------------------
    → TerminatingTerm f nthArg env (TLet x body rest)

  TerminatingCase :
    {d : NameData}                                                -- the name of a datatype
    {@0 varName : NameIn α}                                       -- name of the variable we are pattern matching on (this only supports cases on variables)
    (let iScope = dataIxScope d                                   -- indexes of d
         α'     = α ◂▸ iScope                                     -- general scope + indexes
         iRun   = sing iScope)                                    -- runtime index scope
    {cases : Branches α d (AllNameCon d)}                         -- cases for constructors of dt
    {return : Type (α' ▸ x)}                                      -- return type

    → TerminatingBranches f nthArg env varName (descend $ lookupSt env varName) cases          -- Proof that each branch is terminating

    --------------------------------------------------
    → TerminatingTerm f nthArg env (TCase d iRun (TVar varName) cases return)

  -- Not sure what to do about Annotation, Sort and Pi
{-# COMPILE AGDA2HS TerminatingTerm #-}

data TerminatingTermList {α} f nthArg env where
  TerminatingTermListNil : TerminatingTermList f nthArg env []
  TerminatingTermListCons : 
    {@0 term : Term α}
    {@0 terml : List (Term α)}
    → TerminatingTerm f nthArg env term
    → TerminatingTermList f nthArg env terml
    → TerminatingTermList f nthArg env (term ∷ terml)

{-# COMPILE AGDA2HS TerminatingTermList #-}

data TerminatingTermS {α} f nthArg env where
  TerminatingTermSNil : TerminatingTermS f nthArg env TSNil
  TerminatingTermSCons : 
    {@0 term : Term α}
    {@0 name : Name}
    {@0 terml : (TermS α rβ)}
    → TerminatingTerm f nthArg env term
    → TerminatingTermS f nthArg env terml
    → TerminatingTermS f nthArg env (TSCons {x = name} term terml)
{-# COMPILE AGDA2HS TerminatingTermS #-}

data TerminatingBranches {α = α} {d = d} f nthArg env var rel where
  TerminatingNil : TerminatingBranches f nthArg env var rel BsNil
  TerminatingCons : ∀ {@0 c : NameCon d} {@0 cs : RScope (NameCon d)} {@0 b : Branch α c} {@0 bs : Branches α d cs}
           → TerminatingBranch f nthArg env var rel b
           → TerminatingBranches f nthArg env var rel bs
           → TerminatingBranches f nthArg env var rel (BsCons b bs)
{-# COMPILE AGDA2HS TerminatingBranches #-}

data TerminatingBranch {α = α} {d = d} f nthArg env var rel where
  TerminatingBBranch :
              {@0 c : NameCon d}
              {rhs : Term (α ◂▸ (fieldScope c))}
            → TerminatingTerm f nthArg (updateEnv env (fieldScope c) rel ) rhs
            → TerminatingBranch f nthArg env var rel (BBranch (sing c) ((fieldScope c) ⟨ refl ⟩) rhs)
{-# COMPILE AGDA2HS TerminatingBranch #-}


-- Certificate that a function is decreasing using the guard condition
data Descending (@0 f : FunDefinition) : Set
data Descending f where
   DescendingIndex : 
      -- index of the decreasing parameter
     (nthArg : Maybe (NthArg (arity f)))
     -- certificate that the body of the function is always decreasing in the given parameter
     → (TerminatingTerm f nthArg 
         -- subterm context created from the scope of the arity of the function
         (createStEnvFromScope (arity f)) 
         -- body of the function
         (body f)) 
     → Descending f
{-# COMPILE AGDA2HS Descending #-}
