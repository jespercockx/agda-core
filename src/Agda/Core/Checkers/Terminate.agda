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
  → (env : SubTermEnv α) → (prf : arity f ⊆ α) → (term : Term α) → Either String (TerminatingTerm f nthArg env prf term)

checkDescendingIndexList : (f : FunDefinition) → (nthArg : NthArg (arity f)) 
  → (env : SubTermEnv α) → (prf : arity f ⊆ α) → (terml : List (Term α)) → Either String (TerminatingTermList f nthArg env prf terml)

checkDescendingIndexTermS : (f : FunDefinition) → (nthArg : NthArg (arity f)) 
  → (env : SubTermEnv α) → (prf : arity f ⊆ α) → (terml : TermS α rβ) → Either String (TerminatingTermS f nthArg env prf terml)

checkDescendingIndexApp : (f : FunDefinition) → (nthArg : NthArg (arity f)) 
  → (env : SubTermEnv α) → (prf : arity f ⊆ α) → (term : Term α) → Either String (TerminatingTerm f nthArg env prf term)

checkDescendingIndexBranches : (f : FunDefinition) → (nthArg : NthArg (arity f)) 
  → (env : SubTermEnv α) → (prf : arity f ⊆ α) → {d : NameData} → {@0 cs : RScope (NameCon d)} → (var : NameIn α) → (bs : Branches α d cs) → Either String (TerminatingBranches f nthArg env prf var bs)

checkDescendingIndexBranch : (f : FunDefinition) → (nthArg : NthArg (arity f)) 
  → (env : SubTermEnv α) → (prf : arity f ⊆ α) → {d : NameData} → (@0 c : NameCon d) → (var : NameIn α) → (b : Branch α c) → Either String (TerminatingBranch f nthArg env prf var b)

checkDescendingIndexBranches f nthArg env prf var BsNil = Right TerminatingNil
checkDescendingIndexBranches f nthArg env prf var (BsCons {c} b bs) = 
  mapEither' 
    (λ err → Left err)
    (λ ttb → mapEither'
      (λ err → Left err)
      (λ ttbs → Right $ TerminatingCons ttb ttbs)
      (checkDescendingIndexBranches f nthArg env prf var bs)
    )
    (checkDescendingIndexBranch f nthArg env prf c var b)
{-# COMPILE AGDA2HS checkDescendingIndexBranches #-}

checkDescendingIndexBranch {α} f nthArg env prf c var (BBranch (c2 ⟨ q ⟩) (fields ⟨ p ⟩) rhs) = 
  mapEither'
      (λ err → Left err)
      (λ tt → Right $
        J0
          (λ c' q' → TerminatingBranch f nthArg env prf var
            (BBranch (c' ⟨ q' ⟩) (fields ⟨ p ⟩) rhs))
          q
          (J0
            (λ fs eq → TerminatingBranch f nthArg env prf var
              (BBranch (c ⟨ refl ⟩) (fs ⟨ eq ⟩) rhs))
            p
            (J0
              (λ trm eq → TerminatingBranch f nthArg env prf var (BBranch (c ⟨ refl ⟩) (fieldScope c ⟨ refl ⟩) trm))
              (transSym p rhs)
              (TerminatingBBranch {c = c} $
                J0
                  (λ fs eq →
                    TerminatingTerm f nthArg (updateEnv env fs var)
                      (subExtScope (fs ⟨ refl ⟩) prf)
                      (subst0 (λ f → Term (α ◂▸ f)) (trans p eq) rhs)
                  )
                  (sym p)
                  tt
              )
            )
          )
      )
      (checkDescendingIndex f nthArg (updateEnv env fields var) (subExtScope (sing fields) prf) (subst0 (λ f → Term (α ◂▸ f)) (trans p refl) rhs))
{-# COMPILE AGDA2HS checkDescendingIndexBranch #-}

checkDescendingIndexList f nthArg env prf [] = Right $ TerminatingTermListNil
checkDescendingIndexList f nthArg env prf (x ∷ xs) = 
  mapEither'
    (λ err → Left err)
    (λ tt → mapEither'
      (λ err → Left err)
      (λ ttl → Right $ TerminatingTermListCons tt ttl)
      (checkDescendingIndexList f nthArg env prf xs)
    )
    (checkDescendingIndex f nthArg env prf x)
{-# COMPILE AGDA2HS checkDescendingIndexList #-}

checkDescendingIndexTermS f nthArg env prf TSNil = Right $ TerminatingTermSNil
checkDescendingIndexTermS f nthArg env prf (TSCons x xs) = 
  mapEither'
    (λ err → Left err)
    (λ tt → mapEither'
      (λ err → Left err)
      (λ ttl → Right $ TerminatingTermSCons tt ttl)
      (checkDescendingIndexTermS f nthArg env prf xs)
    )
    (checkDescendingIndex f nthArg env prf x)
{-# COMPILE AGDA2HS checkDescendingIndexTermS #-}


checkDescendingIndexApp f nthArg env prf (TApp func arg) = 
  mapEither' 
    (λ err → Left err) -- case where the argument is nonterminating
    (λ targ → mapEither' 
      (λ err →  Left err)
      (λ tfunc → Right $ TerminatingApp tfunc targ) -- case where arg and func are terminating
      (checkDescendingIndex f nthArg env prf func))
    (checkDescendingIndex f nthArg env prf arg)
checkDescendingIndexApp f nthArg env prf _ = Left "Not an app" 
{-# COMPILE AGDA2HS checkDescendingIndexApp #-}

checkDescendingIndex f nthArg env prf (TVar x) = Right TerminatingVar
checkDescendingIndex f nthArg env prf (TCon c us) = 
  mapEither'
    (λ err → Left err)
    (λ tt → Right $ TerminatingCon tt)
    (checkDescendingIndexTermS f nthArg env prf us)
checkDescendingIndex f nthArg env prf (TLam x body) = fmap TerminatingLam $ checkDescendingIndex f nthArg (StEnvExtend x Nothing env) (subWeaken prf) body
checkDescendingIndex f nthArg env prf (TApp func (TVar x)) = 
  mapEither' 
  -- case where the function isn't directly terminating: have to check whether we are currently looking at the decreasing argument
    (λ err → case (unApps func) of λ where
        (TDef fname , args) {{ eq }} → case 
              (mkpair (decNat (lengthN args) (indexToNat $ indexOf (nthArg)))
              (mkpair (decNamesIn fname (index f)) 
              (mkpair (decMaybeNameIn (lookupSt env x) (Just (weakenNameIn (prf) $ getNthArg nthArg))) 
                      (checkDescendingIndexList f nthArg env prf args)))) of λ where
          (True ⟨ lengthProof ⟩ , (True ⟨ fnameProof ⟩ , (True ⟨ stProof ⟩ , Right awhat))) → Right $ DecreasingNthArgApp (trans (cong fst eq) (cong TDef fnameProof)) (trans (cong lengthN (cong snd eq)) lengthProof) (stProof) (subst0 (TerminatingTermList f nthArg env prf) (sym (cong snd eq)) awhat)
          _ → Left "One of the conditions of the descent of the recursive call was not respected"
        _ → Left "Either one of the arguments or the function was non-terminating, and the function was not named"
    )
    (λ tt → Right tt)
    (checkDescendingIndexApp f nthArg env prf (TApp func (TVar x)))
checkDescendingIndex f nthArg env prf (TApp func arg) = checkDescendingIndexApp f nthArg env prf (TApp func arg) 
checkDescendingIndex f nthArg env prf (TDef funcName) = 
  case (decNamesIn funcName (index f)) of λ where
    (True ⟨ p ⟩) → Left "Impossible: should have matched the App Case"
    (False ⟨ p ⟩) → Right $ TerminatingDef p

checkDescendingIndex f nthArg env prf (TCase d (_ ⟨ p ⟩) (TVar varName) cases return) = 
  mapEither'
    (λ err →  Left err)
    (λ tt → Right $ J0 (λ y' eq → 
      (TerminatingTerm f nthArg env prf (TCase d (y' ⟨ eq ⟩) (TVar varName) cases return))) p (TerminatingCase tt))
      (checkDescendingIndexBranches f nthArg env prf varName cases)

checkDescendingIndex f nthArg env prf term = Left "Not implemented"
{-# COMPILE AGDA2HS checkDescendingIndex #-}

checkTermination' : (f : FunDefinition) → Either String (Descending f)
checkTermination' f = foldr helper (Left "This function is non-terminating") (iterateNthArg (arity f))
  where
    helper : NthArg (arity f) → Either String (Descending f) → Either String (Descending f)
    helper nthArg (Right res) = Right res
    helper nthArg (Left _) = 
      mapRight (DescendingIndex nthArg) 
        (checkDescendingIndex f nthArg (creatStEnvFromScope StEnvEmpty (arity f)) 
          (subst0 (Sub (arity f)) (sym (leftIdentity (f .arity))) subRefl) 
          (subst0 (λ scope → Term scope) (sym (leftIdentity (f .arity))) (body f)))
{-# COMPILE AGDA2HS checkTermination' #-}

checkTermination : {α : Scope Name} → SubTermEnv α → NameIn defScope → Term α → Either String String
checkTermination c def (TLam x body) = checkTermination (StEnvExtend x Nothing c) def body
checkTermination {α} c def body = 
  mapEither'
    (λ err → Left err)
    (λ tt → Right ("The function is terminating in its "))
    (checkTermination' (record { index = def; arity = α; body = body }))
{-# COMPILE AGDA2HS checkTermination #-}



