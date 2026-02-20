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


lookupSt : (Γ : SubTermContext α) (x : NameIn α) → Maybe (NameIn α)
lookupSt StCtxEmpty x = nameInEmptyCase x
lookupSt (StCtxExtend namesubterm nameparent c) name = case (nameInBindCase name
      (λ q → lookupSt c (⟨ _ ⟩ q))
      (λ _ → nameparent)) of λ where
        (Just n) → Just (raiseNameIn (sing _) n)
        Nothing → Nothing
{-# COMPILE AGDA2HS lookupSt #-}


-- opaque
--   unfolding Scope
--
--   caseScope : (α : Scope name)
--             → (@0 {{α ≡ mempty}} → c)
--             → ((@0 x : name) (β : Scope name) → @0 {{α ≡ β ▸ x}} → c)
--             → c
--   caseScope [] emptyCase bindCase = emptyCase
--   caseScope (Erased x ∷ β) emptyCase bindCase = bindCase x β
opaque
  unfolding Scope
  createStCtxFromScope : SubTermContext α → (β : Scope Name)  → SubTermContext (α <> β)
  createStCtxFromScope ctx [] = ctx
  createStCtxFromScope ctx (Erased x ∷ rest) = StCtxExtend x Nothing (createStCtxFromScope ctx rest)

-- datatype for arbitrary member of a scope
data NthArg : @0 Scope Name → Set where
  Zero : (@0 x : Name) → NthArg (α ▸ x)
  Suc : (@0 x : Name) → NthArg α → NthArg (α ▸ x)
{-# COMPILE AGDA2HS NthArg deriving Show #-}

indexOf : NthArg α → Nat
indexOf (Zero _) = zero
indexOf (Suc _ n) = suc (indexOf n)


-- I need a datatype for a function, I don't really like the current one:
-- We need: the arity and the body; if we don't end up converting global env to debruijn indices, then we also need to hold the index of the function, in case of recursive call
-- The day we have corecursive functions, we will need a program datatype encompassing all function definitions, for now we do not handle this
-- Now also we need to decide whether we have the arity and lambda-free body, or just the lambda free body, but I believe since we want to make a statement about a specific parameter index, we should have the arity in the function datatype

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


-- data ArgumentsAgainstDescendingParam (@0 nthArg :  NthArg (arity f)) (@0 ctx : SubTermContext α) → List (Term α) → @0 nthArg :  NthArg (arity f) where
--   AADPNil : 

  -- TyBsCons : ∀ {@0 c : NameCon d} {@0 cs : RScope (NameCon d)} {@0 b : Branch α c} {@0 bs : Branches α d cs}
  --          → TyBranch Γ dt ps rt b
  --          → TyBranches Γ dt ps rt bs
  --          → TyBranches Γ dt ps rt (BsCons b bs)

-- certificate that the body of the function is always decreasing in the given parameter
data TerminatingTerm (@0 f : FunDefinition) (@0 nthArg :  NthArg (arity f)) (@0 ctx : SubTermContext α) : @0 Term α → Set
data TerminatingTerm {α} f nthArg ctx where

  TerminatingLam :
    {@0 body : Term (bind α x)}
    → TerminatingTerm f nthArg (StCtxExtend x Nothing ctx) body 
    → TerminatingTerm f nthArg ctx (TLam x body)

  TerminatingVar :
    {x : NameIn α}
    → TerminatingTerm f nthArg ctx (TVar x)

  -- TerminatingDef : {def : NameIn defScope}
  --   → TerminatingTerm f nthArg ctx (TDef def)
  --
  -- will match on functions such as lambdas, or functions that are not the current one (all functions that can appear in another should have been declared previously, and as such terminiation-checked before this one, hence they are guaranteed to be terminating). Also, there will be the case below, the inductive definition will "peel" the function until we get to the decreasing argument.
  TerminatingApp :
    {@0 function : Term α}
    {@0 argument : Term α}
    → TerminatingTerm f nthArg ctx function 
    → TerminatingTerm f nthArg ctx argument 
    → TerminatingTerm f nthArg ctx (TApp function argument)

  -- case where the last argument is the decreasing one (match on size of args ig?)
  -- difference with previous one is that function is not guaranteed to be terminating, since the statement we are making is that it is if it is always decreasing on this argument
  -- If we keep it simple, we should have that the recursive call can only be done on variable (one declared through a pattern-match)
  -- One question i guess is, which is it necessary for it to be "peeled off", like why can't we just get nth argument even if there are more than n?
  -- I guess a good reason is if we want to have the return terminating term to be on a TApp, this way we check that the number of args in the inner function is "ntharg 1"
  -- DecreasingNthArgApp :
  --   {@0 function : Term α}
  --   {@0 x : NameIn α}
  --   (let (func , args) = unApps function)
  --
  --   → @0 func ≡ TDef (index f)
  --   → @0 lengthNat args ≡ indexOf nthArg
  --   → @0 lookupSt ctx x ≡ Just (arity)
  --   -- here we need both a proof that there are the right amount of arguments in args (ntharg - 1), and a proof that x is a subterm of the nth parameters of f
  --   → TerminatingTerm f nthArg ctx (TApp function (TVar x))


  -- TerminatingOtherFuncApp :
  --   {term : Term α}
  --   {@0 def : NameIn defScope}
  --   -- (let funcargs = unApps term
  --   --      func = fst funcargs
  --   --      args = snd funcargs
  --   (let (func , args) = unApps term)
  --   → @0 func ≡ TDef def
  --   → @0 Not (def ≡ index f)
  --   → @0 ListAll (λ arg → TerminatingTerm f nthArg ctx arg) args
  --   → TerminatingTerm f nthArg ctx term
  --
  -- TerminatingLambdaApp :
  --   {term : Term α}
  --   -- {@0 def : NameIn defScope}
  --   (let funcargs = unApps term
  --        func = fst funcargs
  --        args = snd funcargs
  --   )
  --   → @0 Not (∃[ def ∈ NameIn defScope ] (func ≡ TDef def))
  --   → @0 ListAll (λ arg → TerminatingTerm f nthArg ctx arg) args
  --   → TerminatingTerm f nthArg ctx term
  --
  -- TerminatingDecreasingArgApp :
  --   {term : Term α}
  --   {@0 def : NameIn defScope}
  --   (let funcargs = unApps term
  --        func = fst funcargs
  --        args = snd funcargs
  --   )
  --   → @0 func ≡ TDef def
  --   → @0 def ≡ index f
  --   → @0 ListAll (λ arg → TerminatingTerm f nthArg ctx arg) args
  --   → TerminatingTerm f nthArg ctx term


{-# COMPILE AGDA2HS TerminatingTerm #-}


-- Certificate that a function is decreasing using the guard condition
data Descending (@0 f : FunDefinition) : @0 NthArg (arity f) → Set
data Descending f where
   -- Only possible constructor: 
   DescendingIndex : 
      -- index of the decreasing parameter
      {nthArg : (NthArg (arity f))}
     -- certificate that the body of the function is always decreasing in the given parameter
     → (TerminatingTerm f nthArg 
         -- subterm context created from the scope of the arity of the function
         (createStCtxFromScope StCtxEmpty (arity f)) 
         -- body of the function
         (subst0 (λ scope → Term scope) (sym (leftIdentity (f .arity))) (body f))) 
     → Descending f nthArg
{-# COMPILE AGDA2HS Descending #-}

-- Here well need to show that for all recursive calls within body f, the argument corresponding to the NameIn (arity f) will be always decreasing
-- However, it does not really make sense to have it as a nameIn, since we will have to match on index of the argument anyways (itll be under the form : (TApp (... (TDef index) .1. ...) .N.)) where .1. to .N. are the arguments
--
-- So recipe: in Descending we have a nameIn arity, which we need to "pattern match" into its "IsNth" component, to know which argument it is. But then that means decomposing applications in the same way. Maybe it would make more sense to create a new "numbering" datastructure, like "NthArg", which would work in combination with unapps, 
-- Question, is it necessary or even interesting to have NthArg be indexed over a scope? Would be be too arbitrary to have it be just a natural number equivalent



-- data TyTerm {α} Γ where

  -- TyCase :
  --   {d : NameData}                                                -- the name of a datatype
  --   (let pScope = dataParScope d                                  -- parameters of d
  --        iScope = dataIxScope d                                   -- indexes of d
  --        α'     = α ◂▸ iScope                               -- general scope + indexes
  --        dt     = sigData sig d                                   -- the datatype called d
  --        iRun   = sing iScope)                                    -- runtime index scope
  --   {@0 pars : TermS α pScope}                                    -- parameters of d in Scope α
  --   {@0 ixs  : TermS α iScope}                                    -- indexes of d in Scope α
  --   (let ixs' : TermS α' iScope                                   -- indexes of d in Scope α'
  --        ixs' = weaken (subExtScope iRun subRefl) ixs
  --        α'Subst : α' ⇒ α                                         -- subst of α' to α
  --        α'Subst = extSubst (idSubst (singScope Γ)) ixs)
  --   {cases : Branches α d (AllNameCon d)}                         -- cases for constructors of dt
  --   {return : Type (α' ▸ x)}                                      -- return type
  --   (let αInα' : α ⊆ α'
  --        αInα' = subExtScope iRun subRefl                         -- proof that α is in α'
  --        Γ' : Context α'                                          -- new context with α and the indexes
  --        Γ' = addContextTel Γ (instDataIxTel dt pars)
  --        tx : Type α'
  --        tx = dataType d (weaken αInα' k) (weaken αInα' pars) ixs'
  --        return' : Type α
  --        return' = subst (α'Subst ▹ x ↦ u) return)
  --
  --   → Γ' , x ∶ tx ⊢ unType return ∶ sortType (typeSort return)    -- if return is well formed
  --   → TyBranches Γ dt pars return cases                           -- if each case is well typed
  --   → Γ ⊢ u ∶ dataType d k pars ixs                               -- if u is well typed
  --   --------------------------------------------------
  --   → Γ ⊢ TCase d iRun u cases return ∶ return'                   -- then the branching on u is well typed
