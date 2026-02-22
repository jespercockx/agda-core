open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.Rules.Conversion
open import Agda.Core.Rules.Typing

module Agda.Core.Rules.Terminating
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x      : Name
  @0 α      : Scope Name
  @0 rβ     : RScope Name
  @0 u v    : Term α
  @0 a b c  : Type α
  @0 k l    : Sort α


data SubTermContext : @0 Scope Name → Set where
  StCtxEmpty  : SubTermContext mempty
  StCtxExtend : (@0 x : Name) → Maybe (NameIn α) → SubTermContext α → SubTermContext (α ▸ x) -- here x, is a subterm of y.
{-# COMPILE AGDA2HS SubTermContext #-}

private -- it should use a RScope instead of β and then could be public
  raiseNameIn : {@0 α β : Scope Name} → Singleton β → NameIn α →  NameIn (α <> β)
  raiseNameIn r n = weakenNameIn (subJoinDrop r subRefl) n
  {-# COMPILE AGDA2HS raiseNameIn #-}

opaque
  unfolding RScope extScope
  updateEnv : SubTermContext α → (cs : RScope Name) → NameIn α → SubTermContext (extScope α cs)
  updateEnv env [] _ = env
  updateEnv env (Erased x ∷ s) name = updateEnv (StCtxExtend x (Just name) env) s (weakenNameIn (subWeaken subRefl) name)
  {-# COMPILE AGDA2HS updateEnv #-}




lookupSt : (Γ : SubTermContext α) (x : NameIn α) → Maybe (NameIn α)
lookupSt StCtxEmpty x = nameInEmptyCase x
lookupSt (StCtxExtend namesubterm nameparent c) name = case (nameInBindCase name
      (λ q → lookupSt c (⟨ _ ⟩ q))
      (λ _ → nameparent)) of λ where
        (Just n) → Just (raiseNameIn (sing _) n)
        Nothing → Nothing
{-# COMPILE AGDA2HS lookupSt #-}

opaque
  unfolding Scope
  createStCtxFromScope : SubTermContext α → (β : Scope Name)  → SubTermContext (α <> β)
  createStCtxFromScope ctx [] = ctx
  createStCtxFromScope ctx (Erased x ∷ rest) = StCtxExtend x Nothing (createStCtxFromScope ctx rest)
{-# COMPILE AGDA2HS createStCtxFromScope #-}

-- datatype for arbitrary member of a scope
data NthArg : @0 Scope Name → Set where
  Zero : (@0 x : Name) → NthArg (α ▸ x)
  Suc : (@0 x : Name) → NthArg α → NthArg (α ▸ x)
{-# COMPILE AGDA2HS NthArg deriving Show #-}

indexOf : NthArg α → Nat
indexOf (Zero _) = zero
indexOf (Suc _ n) = suc (indexOf n)

opaque
  unfolding Scope
  getNthArg : NthArg α → NameIn α
  getNthArg (Zero x) = ⟨ x ⟩  (Zero ⟨ IsZero refl ⟩)
  getNthArg {α} (Suc x next)  = weakenNameIn (subWeaken subRefl) (getNthArg next)

record FunDefinition : Set where
  no-eta-equality
  field
    index : NameIn defScope
    arity : Scope Name 
    body : Term arity
open FunDefinition public
{-# COMPILE AGDA2HS FunDefinition deriving Show #-}

Not : Set → Set
Not A = A → ⊥

data ListAll {A : Set} (P : A → Set) : List A → Set where
  []  : ListAll P []
  _∷_ : {x : A} {xs : List A} → P x → ListAll P xs → ListAll P (x ∷ xs)

data TerminatingBranches {@0 d : NameData} (@0 f : FunDefinition) (@0 nthArg :  NthArg (arity f)) (@0 ctx : SubTermContext α) (@0 prf : arity f ⊆ α) (@0 patternMatchedVariable : NameIn α) : {@0 cs : RScope (NameCon d)} → (@0 bs : Branches α d cs) → Set
data TerminatingTerm (@0 f : FunDefinition) (@0 nthArg : NthArg (arity f)) (@0 ctx : SubTermContext α) : @0 arity f ⊆ α → @0 Term α → Set
data TerminatingBranch {@0 d : NameData} (@0 f : FunDefinition) (@0 nthArg :  NthArg (arity f)) (@0 ctx : SubTermContext α) (@0 prf : arity f ⊆ α) (@0 patternMatchedVariable : NameIn α) : {@0 c : NameCon d} → @0 Branch α c → Set

data TerminatingBranches {α = α} {d = d} f nthArg ctx prf var where
  TerminatingNil : TerminatingBranches f nthArg ctx prf var BsNil
  TerminatingCons : ∀ {@0 c : NameCon d} {@0 cs : RScope (NameCon d)} {@0 b : Branch α c} {@0 bs : Branches α d cs}
           → TerminatingBranch f nthArg ctx prf var b
           → TerminatingBranches f nthArg ctx prf var bs
           → TerminatingBranches f nthArg ctx prf var (BsCons b bs)
{-# COMPILE AGDA2HS TerminatingBranches #-}

data TerminatingBranch {α = α} {d = d} f nthArg ctx prf var where
  TerminatingBBranch : 
              (c : NameCon d)
              (let fields = fieldScope c
                   α' = α ◂▸ fields
                   r = sing fields)
              (rhs : Term α')
            → TerminatingTerm f nthArg (updateEnv ctx fields var) (subExtScope (sing fields) prf) rhs -- the rhs of the clause (whose environment got extended) needs to be terminating
            → TerminatingBranch f nthArg ctx prf var (BBranch (sing c) r rhs)
{-# COMPILE AGDA2HS TerminatingBranch #-}

-- certificate that the body of the function is always decreasing in the given parameter
data TerminatingTerm {α} f nthArg ctx where

  TerminatingVar :
    {x : NameIn α}
    {@0 prf : arity f ⊆ α}
    --------------------------------------------------------------
    → TerminatingTerm f nthArg ctx prf (TVar x)

  TerminatingApp :
    {@0 function : Term α}
    {@0 argument : Term α}
    {@0 prf : arity f ⊆ α}
    → TerminatingTerm f nthArg ctx prf function 
    → TerminatingTerm f nthArg ctx prf argument 
    --------------------------------------------------------------
    → TerminatingTerm f nthArg ctx prf (TApp function argument)

  DecreasingNthArgApp :
    {@0 function : Term α}
    {@0 x : NameIn α} -- The argument is a variable (TVar)
    {@0 prf : arity f ⊆ α}
    (let (func , args) = unApps function)

    → @0 func ≡ TDef (index f)
    → @0 lengthNat args ≡ indexOf nthArg -- The number of arguments to the left of that application corresponds to the index of the decreasing parameter
    → @0 lookupSt ctx x ≡ Just (weakenNameIn (prf) $ getNthArg nthArg) -- The argument corresponding to the decreasing parameter is indeed a subterm of said parameter
    --------------------------------------------------------------
    → TerminatingTerm f nthArg ctx prf (TApp function (TVar x))

  -- We can use this because we assume all functions defined up to that point have been termination checked themselves, which itself assumes corecursion is not handled, which it isn't yet.
  TerminatingDef :
    {@0 functionName : NameIn defScope}
    {@0 prf : arity f ⊆ α}
    → @0 Not (functionName ≡ index f)
    --------------------------------------------------------------
    → TerminatingTerm f nthArg ctx prf (TDef functionName)

  TerminatingLam :
    {@0 body : Term (bind α x)}
    {@0 prf : arity f ⊆ α}
    → TerminatingTerm f nthArg (StCtxExtend x Nothing ctx) (subWeaken prf) body 
    --------------------------------------------------------------
    → TerminatingTerm f nthArg ctx prf (TLam x body)

  TerminatingCase :
    {d : NameData}                                                -- the name of a datatype
    {@0 prf : arity f ⊆ α}
    {@0 varName : NameIn α}                                       -- name of the variable we are pattern matching on (this only supports cases on variables)
    (let iScope = dataIxScope d                                   -- indexes of d
         α'     = α ◂▸ iScope                                     -- general scope + indexes
         iRun   = sing iScope)                                    -- runtime index scope
    {cases : Branches α d (AllNameCon d)}                         -- cases for constructors of dt
    {return : Type (α' ▸ x)}                                      -- return type

    → TerminatingBranches f nthArg ctx prf varName cases          -- Proof that each branch is terminating

    --------------------------------------------------
    → TerminatingTerm f nthArg ctx prf (TCase d iRun (TVar varName) cases return)

{-# COMPILE AGDA2HS TerminatingTerm #-}


-- Certificate that a function is decreasing using the guard condition
data Descending (@0 f : FunDefinition) : Set
data Descending f where

   DescendingIndex : 
      -- index of the decreasing parameter
     (nthArg : (NthArg (arity f)))
     -- certificate that the body of the function is always decreasing in the given parameter
     → (TerminatingTerm f nthArg 
         -- subterm context created from the scope of the arity of the function
         (createStCtxFromScope StCtxEmpty (arity f)) 
         (subst0 (Sub (arity f)) (sym (leftIdentity (f .arity))) subRefl)
         -- body of the function
         (subst0 (λ scope → Term scope) (sym (leftIdentity (f .arity))) (body f))) 
     → Descending f
{-# COMPILE AGDA2HS Descending #-}
