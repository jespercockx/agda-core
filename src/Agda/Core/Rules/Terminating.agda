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


-- data ArgumentsAgainstDescendingParam (@0 nthArg :  NthArg (arity f)) (@0 ctx : SubTermContext α) → List (Term α) → @0 nthArg :  NthArg (arity f) where
--   AADPNil : 

  -- TyBsCons : ∀ {@0 c : NameCon d} {@0 cs : RScope (NameCon d)} {@0 b : Branch α c} {@0 bs : Branches α d cs}
  --          → TyBranch Γ dt ps rt b
  --          → TyBranches Γ dt ps rt bs
  --          → TyBranches Γ dt ps rt (BsCons b bs)

-- certificate that the body of the function is always decreasing in the given parameter
data TerminatingTerm (@0 f : FunDefinition) (@0 nthArg :  NthArg (arity f)) (@0 ctx : SubTermContext α) : @0 arity f ⊆ α → @0 Term α → Set
data TerminatingTerm {α} f nthArg ctx where

  TerminatingLam :
    {@0 body : Term (bind α x)}
    {@0 prf : arity f ⊆ α}
    → TerminatingTerm f nthArg (StCtxExtend x Nothing ctx) (subWeaken prf) body 
    --------------------------------------------------------------
    → TerminatingTerm f nthArg ctx prf (TLam x body)

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
    {@0 argument : Term α}
    {@0 prf : arity f ⊆ α}
    → @0 Not (functionName ≡ index f)
    --------------------------------------------------------------
    → TerminatingTerm f nthArg ctx prf (TApp (TDef functionName) argument)
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
         (subst0 (Sub (arity f)) (sym (leftIdentity (f .arity))) subRefl)
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
