open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Syntax.TerminationUtils
open import Agda.Core.Rules.Terminating


module Agda.Core.Checkers.Terminate
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

{-# NON_TERMINATING #-} -- need to find a way to not need those
checkDescendingIndex : (f : FunDefinition) → (nthArg : NthArg (arity f))
  → (env : SubTermEnv (arity f) α) → (prf : arity f ⊆ α) → (term : Term α) → Either String (TerminatingTerm f nthArg env prf term)

checkDescendingIndexList : (f : FunDefinition) → (nthArg : NthArg (arity f)) 
  → (env : SubTermEnv (arity f) α) → (prf : arity f ⊆ α) → (terml : List (Term α)) → Either String (TerminatingTermList f nthArg env prf terml)

checkDescendingIndexTermS : (f : FunDefinition) → (nthArg : NthArg (arity f)) 
  → (env : SubTermEnv (arity f) α) → (prf : arity f ⊆ α) → (terml : TermS α rβ) → Either String (TerminatingTermS f nthArg env prf terml)

checkDescendingIndexApp : (f : FunDefinition) → (nthArg : NthArg (arity f)) 
  → (env : SubTermEnv (arity f) α) → (prf : arity f ⊆ α) → (term : Term α) → Either String (TerminatingTerm f nthArg env prf term)

checkDescendingIndexBranches : (f : FunDefinition) → (nthArg : NthArg (arity f)) 
  → (env : SubTermEnv (arity f) α) → (prf : arity f ⊆ α) → {d : NameData} → {@0 cs : RScope (NameCon d)} → (var : NameIn α) → (rel : Relation (arity f)) → (bs : Branches α d cs) → Either String (TerminatingBranches f nthArg env prf var rel bs)

checkDescendingIndexBranch : (f : FunDefinition) → (nthArg : NthArg (arity f)) 
  → (env : SubTermEnv (arity f) α) → (prf : arity f ⊆ α) → {d : NameData} → (@0 c : NameCon d) → (var : NameIn α) → (rel : Relation (arity f)) → (b : Branch α c) → Either String (TerminatingBranch f nthArg env prf var rel b)

checkDescendingIndexBranches f nthArg env prf var rel BsNil = Right TerminatingNil
checkDescendingIndexBranches f nthArg env prf var rel (BsCons {c} b bs) = do
  tb ← checkDescendingIndexBranch f nthArg env prf c var rel b
  tbs ← checkDescendingIndexBranches f nthArg env prf var rel bs
  Right $ TerminatingCons tb tbs
{-# COMPILE AGDA2HS checkDescendingIndexBranches #-}


checkDescendingIndexBranch {α} f nthArg env prf c var rel (BBranch (c2 ⟨ q ⟩) (fields ⟨ p ⟩) rhs) = do
  trhs ← (checkDescendingIndex f nthArg (updateEnv env fields rel) (subExtScope (sing fields) prf) (subst0 (λ f → Term (α ◂▸ f)) (trans p refl) rhs))
  return $ J0
    (λ c' q' → TerminatingBranch f nthArg env prf var rel
      (BBranch (c' ⟨ q' ⟩) (fields ⟨ p ⟩) rhs))
    q
    (J0
      (λ fs eq → TerminatingBranch f nthArg env prf var rel
        (BBranch (c ⟨ refl ⟩) (fs ⟨ eq ⟩) rhs))
      p
      (J0
        (λ trm eq → TerminatingBranch f nthArg env prf var rel (BBranch (c ⟨ refl ⟩) (fieldScope c ⟨ refl ⟩) trm))
        (transSym p rhs)
        (TerminatingBBranch {c = c} $
          J0
            (λ fs eq →
              TerminatingTerm f nthArg (updateEnv env fs rel)
                (subExtScope (fs ⟨ refl ⟩) prf)
                (subst0 (λ f → Term (α ◂▸ f)) (trans p eq) rhs)
            )
            (sym p)
            trhs
        )
      )
    )
{-# COMPILE AGDA2HS checkDescendingIndexBranch #-}

checkDescendingIndexList f nthArg env prf (x ∷ xs) = do
  tth ← checkDescendingIndex f nthArg env prf x
  ttl ← checkDescendingIndexList f nthArg env prf xs
  Right $ TerminatingTermListCons tth ttl
checkDescendingIndexList f nthArg env prf [] = Right $ TerminatingTermListNil
{-# COMPILE AGDA2HS checkDescendingIndexList #-}

checkDescendingIndexTermS f nthArg env prf TSNil = Right $ TerminatingTermSNil
checkDescendingIndexTermS f nthArg env prf (TSCons x xs) = do
  tth ← checkDescendingIndex f nthArg env prf x
  ttl ← checkDescendingIndexTermS f nthArg env prf xs
  Right $ TerminatingTermSCons tth ttl
{-# COMPILE AGDA2HS checkDescendingIndexTermS #-}


checkDescendingIndexApp f nthArg env prf (TApp func arg) = do
  targ ← checkDescendingIndex f nthArg env prf arg
  tfunc ←  checkDescendingIndex f nthArg env prf func
  Right $ TerminatingApp tfunc targ
checkDescendingIndexApp f nthArg env prf _ = Left "Not an app" 
{-# COMPILE AGDA2HS checkDescendingIndexApp #-}

checkDescendingIndex f nthArg env prf (TVar x) = Right TerminatingVar
checkDescendingIndex f nthArg env prf (TCon c us) = do
  tus ← checkDescendingIndexTermS f nthArg env prf us
  Right $ TerminatingCon tus
checkDescendingIndex f nthArg env prf (TLam x body) = fmap TerminatingLam $ checkDescendingIndex f nthArg (StEnvExtend x Unrelated env) (subWeaken prf) body
checkDescendingIndex f nthArg env prf (TApp func (TVar x)) = do
  catchEither (checkDescendingIndexApp f nthArg env prf (TApp func (TVar x))) $ λ err →
    case unApps func of λ where
      (TDef fname , args) {{ eq }} → do
        let lengthOk  = decIndex (lengthN args) (indexOf (lengthScope $ arity f) nthArg)
            fnameOk   = decNamesIn fname (index f)
            stOk      = decRelation (lookupSt env x) (Decreasing (getNthArg nthArg))
        (True ⟨ lengthProof ⟩) ← Right lengthOk
          where _ → Left err
        (True ⟨ fnameProof ⟩)  ← Right fnameOk
          where _ → Left err
        (True ⟨ stProof ⟩)     ← Right stOk
          where _ → Left "The argument corresponding to the descending parameter was not descending"
        argsAllDescending ← checkDescendingIndexList f nthArg env prf args
        Right $ DecreasingNthArgApp
          (trans (cong fst eq) (cong TDef fnameProof))
          (trans (cong lengthN (cong snd eq)) lengthProof)
          stProof
          (subst0 (TerminatingTermList f nthArg env prf) (sym (cong snd eq)) argsAllDescending)
      _ → Left "Either one of the arguments or the function was non-terminating, and the function was not named"
checkDescendingIndex f nthArg env prf (TApp func arg) = checkDescendingIndexApp f nthArg env prf (TApp func arg) 
checkDescendingIndex f nthArg env prf (TDef funcName) = 
  case (decNamesIn funcName (index f)) of λ where
    (True ⟨ p ⟩) → Left "Impossible: should have matched the App Case"
    (False ⟨ p ⟩) → Right $ TerminatingDef p

checkDescendingIndex f nthArg env prf (TCase d (_ ⟨ p ⟩) (TVar varName) cases return) = do
  let rel = descend (lookupSt env varName)
  tbs ← checkDescendingIndexBranches f nthArg env prf varName rel cases
  Right $ J0 (λ y' eq → 
      (TerminatingTerm f nthArg env prf (TCase d (y' ⟨ eq ⟩) (TVar varName) cases return))) p (TerminatingCase tbs)

checkDescendingIndex f nthArg env prf term = Left "Not implemented"
{-# COMPILE AGDA2HS checkDescendingIndex #-}

checkTermination' : (f : FunDefinition) → Either String (Descending f)
checkTermination' f = foldr helper (Left "This function is non-terminating") (iterateNthArg (arity f))
  where
    helper : NthArg (arity f) → Either String (Descending f) → Either String (Descending f)
    helper nthArg (Right res) = Right res
    helper nthArg (Left _) = do
      descBody <- (checkDescendingIndex f nthArg (createStEnvFromScope (arity f)) 
                    subRefl 
                    (body f))
      Right $ DescendingIndex nthArg descBody
{-# COMPILE AGDA2HS checkTermination' #-}

checkTermination : {α : Scope Name} → Scope Name → NameIn defScope → Term α → Either String String
checkTermination c def (TLam x body) = checkTermination (c <> singleton x) def body
checkTermination {α} c def body = do
  DescendingIndex r i ← checkTermination' (record { index = def; arity = α; body = body })
  let env = createStEnvFromScope c
  Right ("The function is terminating in its " ++ show r)
{-# COMPILE AGDA2HS checkTermination #-}



