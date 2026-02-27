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


botErased : {a : Set} → @0 ⊥ → a
botErased ()

private open module @0 G = Globals globals

mapEitherPermissive : {a b c d : Set} → (a → Either c d) → (b → Either c d) → Either a b → Either c d
mapEitherPermissive f g = either f g

eqNatSound : ∀ {x y : Nat} → (x == y) ≡ True → x ≡ y
eqNatSound {zero} {zero} h = refl
eqNatSound {suc n} {suc m} h = cong suc (eqNatSound h)
eqNatSound {zero} {suc _} ()
eqNatSound {suc _} {zero} ()

eqNatSoundFalse : ∀ {x y : Nat} → (x == y) ≡ False → (x ≡ y → ⊥)
eqNatSoundFalse {zero}  {zero}  h _ = case h of λ ()
eqNatSoundFalse {suc n} {suc m} h refl = eqNatSoundFalse {n} {m} h refl
eqNatSoundFalse {zero}  {suc _} h ()
eqNatSoundFalse {suc _} {zero}  h ()

decNat : ∀ (x y : Nat) → Dec (x ≡ y)
decNat x y = case (x == y) of λ where
  True {{ eq }} → True ⟨ eqNatSound eq ⟩
  False {{ eq }} → False ⟨ eqNatSoundFalse eq ⟩
{-# COMPILE AGDA2HS decNat #-}

decMaybeNameIn : ∀ (x y : Maybe (NameIn α)) → Dec (x ≡ y)
decMaybeNameIn (Just a) (Just b) = case decNamesIn a b of λ where
  (True  ⟨ p ⟩) → True  ⟨ cong Just p ⟩
  (False ⟨ f ⟩) → False ⟨ (λ where refl → botErased (f refl)) ⟩
decMaybeNameIn Nothing  Nothing  = True ⟨ refl ⟩
decMaybeNameIn (Just _) Nothing  = False ⟨ (λ ()) ⟩
decMaybeNameIn Nothing  (Just _) = False ⟨ (λ ()) ⟩
{-# COMPILE AGDA2HS decMaybeNameIn #-}


opaque
  unfolding Scope
  iterateNthArg : (α : Scope Name) → List (NthArg α)
  iterateNthArg [] = []
  iterateNthArg (Erased x ∷ tl) = ZeroNA x ∷ (map (SucNA x) (iterateNthArg tl))
{-# COMPILE AGDA2HS iterateNthArg #-}


{-# NON_TERMINATING #-} -- need to find a way to not need those
checkDescendingIndex : (f : FunDefinition) → (nthArg : NthArg (arity f)) → (ctx : SubTermContext α) → (prf : arity f ⊆ α) → (term : Term α) → Either String (TerminatingTerm f nthArg ctx prf term)

checkDescendingIndexList : (f : FunDefinition) → (nthArg : NthArg (arity f)) → (ctx : SubTermContext α) → (prf : arity f ⊆ α) → (terml : List (Term α)) → Either String (TerminatingTermList f nthArg ctx prf terml)

checkDescendingIndexTermS : (f : FunDefinition) → (nthArg : NthArg (arity f)) → (ctx : SubTermContext α) → (prf : arity f ⊆ α) → (terml : TermS α rβ) → Either String (TerminatingTermS f nthArg ctx prf terml)

checkDescendingIndexApp : (f : FunDefinition) → (nthArg : NthArg (arity f)) → (ctx : SubTermContext α) → (prf : arity f ⊆ α) → (term : Term α) → Either String (TerminatingTerm f nthArg ctx prf term)

checkDescendingIndexBranches : (f : FunDefinition) → (nthArg : NthArg (arity f)) → (ctx : SubTermContext α) → (prf : arity f ⊆ α) → {d : NameData} → {@0 cs : RScope (NameCon d)} → (var : NameIn α) → (bs : Branches α d cs) → Either String (TerminatingBranches f nthArg ctx prf var bs)

checkDescendingIndexBranch : (f : FunDefinition) → (nthArg : NthArg (arity f)) → (ctx : SubTermContext α) → (prf : arity f ⊆ α) → {d : NameData} → (@0 c : NameCon d) → (var : NameIn α) → (b : Branch α c) → Either String (TerminatingBranch f nthArg ctx prf var b)

checkDescendingIndexBranches f nthArg ctx prf var BsNil = Right TerminatingNil
checkDescendingIndexBranches f nthArg ctx prf var (BsCons {c} b bs) = 
  mapEitherPermissive 
    (λ err → Left err)
    (λ ttb → mapEitherPermissive
      (λ err → Left err)
      (λ ttbs → Right $ TerminatingCons ttb ttbs)
      (checkDescendingIndexBranches f nthArg ctx prf var bs)
    )
    (checkDescendingIndexBranch f nthArg ctx prf c var b)
{-# COMPILE AGDA2HS checkDescendingIndexBranches #-}

transSym : {x y : RScope Name} (p : x ≡ y) → (t : Term (α ◂▸ x)) → subst0 (λ (@0 f₁) → Term (α ◂▸ f₁)) (trans p (sym p)) t ≡ t
transSym refl _ = refl

subst2 : {A : Set} {x y : A} {P : A → Set} → x ≡ y → P x → P y
subst2 refl px = px

checkDescendingIndexBranch {α} f nthArg ctx prf c var (BBranch (c2 ⟨ q ⟩) (fields ⟨ p ⟩) rhs) = 
  mapEitherPermissive
      (λ err → Left err)
      (λ tt → Right $
        J0
          (λ c' q' → TerminatingBranch f nthArg ctx prf var
            (BBranch (c' ⟨ q' ⟩) (fields ⟨ p ⟩) rhs))
          q
          (J0
            (λ fs eq → TerminatingBranch f nthArg ctx prf var
              (BBranch (c ⟨ refl ⟩) (fs ⟨ eq ⟩) rhs))
            p
            (J0
              (λ trm eq → TerminatingBranch f nthArg ctx prf var (BBranch (c ⟨ refl ⟩) (fieldScope c ⟨ refl ⟩) trm))
              (transSym p rhs)
              (TerminatingBBranch {c = c} $
                J0
                  (λ fs eq →
                    TerminatingTerm f nthArg (updateEnv ctx fs var)
                      (subExtScope (fs ⟨ refl ⟩) prf)
                      (subst0 (λ f → Term (α ◂▸ f)) (trans p eq) rhs)
                  )
                  (sym p)
                  tt
              )
            )
          )
      )
      (checkDescendingIndex f nthArg (updateEnv ctx fields var) (subExtScope (sing fields) prf) (subst0 (λ f → Term (α ◂▸ f)) (trans p refl) rhs))
{-# COMPILE AGDA2HS checkDescendingIndexBranch #-}

checkDescendingIndexList f nthArg ctx prf [] = Right $ TerminatingTermListNil
checkDescendingIndexList f nthArg ctx prf (x ∷ xs) = 
  mapEitherPermissive
    (λ err → Left err)
    (λ tt → mapEitherPermissive
      (λ err → Left err)
      (λ ttl → Right $ TerminatingTermListCons tt ttl)
      (checkDescendingIndexList f nthArg ctx prf xs)
    )
    (checkDescendingIndex f nthArg ctx prf x)
{-# COMPILE AGDA2HS checkDescendingIndexList #-}

checkDescendingIndexTermS f nthArg ctx prf TSNil = Right $ TerminatingTermSNil
checkDescendingIndexTermS f nthArg ctx prf (TSCons x xs) = 
  mapEitherPermissive
    (λ err → Left err)
    (λ tt → mapEitherPermissive
      (λ err → Left err)
      (λ ttl → Right $ TerminatingTermSCons tt ttl)
      (checkDescendingIndexTermS f nthArg ctx prf xs)
    )
    (checkDescendingIndex f nthArg ctx prf x)
{-# COMPILE AGDA2HS checkDescendingIndexTermS #-}


checkDescendingIndexApp f nthArg ctx prf (TApp func arg) = 
  mapEitherPermissive 
    (λ err → Left err) -- case where the argument is nonterminating
    (λ targ → mapEitherPermissive 
      (λ err →  Left err)
      (λ tfunc → Right $ TerminatingApp tfunc targ) -- case where arg and func are terminating
      (checkDescendingIndex f nthArg ctx prf func))
    (checkDescendingIndex f nthArg ctx prf arg)
checkDescendingIndexApp f nthArg ctx prf _ = Left "Not an app" 
{-# COMPILE AGDA2HS checkDescendingIndexApp #-}

checkDescendingIndex f nthArg ctx prf (TVar x) = Right TerminatingVar
checkDescendingIndex f nthArg ctx prf (TCon c us) = 
  mapEitherPermissive
    (λ err → Left err)
    (λ tt → Right $ TerminatingCon tt)
    (checkDescendingIndexTermS f nthArg ctx prf us)
checkDescendingIndex f nthArg ctx prf (TLam x body) = fmap TerminatingLam $ checkDescendingIndex f nthArg (StCtxExtend x Nothing ctx) (subWeaken prf) body
checkDescendingIndex f nthArg ctx prf (TApp func (TVar x)) = 
  mapEitherPermissive 
  -- case where the function isn't directly terminating: have to check whether we are currently looking at the decreasing argument
    (λ err → case (unApps func) of λ where
        (TDef fname , args) {{ eq }} → case 
              (mkpair (decNat (lengthN args) (indexToNat $ indexOf (nthArg)))
              (mkpair (decNamesIn fname (index f)) 
              (mkpair (decMaybeNameIn (lookupSt ctx x) (Just (weakenNameIn (prf) $ getNthArg nthArg))) 
                      (checkDescendingIndexList f nthArg ctx prf args)))) of λ where
          (True ⟨ lengthProof ⟩ , (True ⟨ fnameProof ⟩ , (True ⟨ stProof ⟩ , Right awhat))) → Right $ DecreasingNthArgApp (trans (cong fst eq) (cong TDef fnameProof)) (trans (cong lengthN (cong snd eq)) lengthProof) (stProof) (subst0 (TerminatingTermList f nthArg ctx prf) (sym (cong snd eq)) awhat)
          _ → Left "Didn't work"
        _ → Left "Didn't work"
    )
    (λ tt → Right tt)
    (checkDescendingIndexApp f nthArg ctx prf (TApp func (TVar x)))
checkDescendingIndex f nthArg ctx prf (TApp func arg) = checkDescendingIndexApp f nthArg ctx prf (TApp func arg) 
checkDescendingIndex f nthArg ctx prf (TDef funcName) = 
  case (decNamesIn funcName (index f)) of λ where
    (True ⟨ p ⟩) → Left "Impossible: should have matched the App Case"
    (False ⟨ p ⟩) → Right $ TerminatingDef p

checkDescendingIndex f nthArg ctx prf (TCase d (_ ⟨ p ⟩) (TVar varName) cases return) = 
  mapEitherPermissive
    (λ err →  Left err)
    (λ tt → Right $ J0 (λ y' eq → 
      (TerminatingTerm f nthArg ctx prf (TCase d (y' ⟨ eq ⟩) (TVar varName) cases return))) p (TerminatingCase tt))
      (checkDescendingIndexBranches f nthArg ctx prf varName cases)

checkDescendingIndex f nthArg ctx prf term = Left "Not implemented"
{-# COMPILE AGDA2HS checkDescendingIndex #-}

checkTermination' : (f : FunDefinition) → Either String (Descending f)
checkTermination' f = foldr helper (Left "This function is non-terminating") (iterateNthArg (arity f))
  where
    helper : NthArg (arity f) → Either String (Descending f) → Either String (Descending f)
    helper nthArg (Right res) = Right res
    helper nthArg (Left _) = 
      mapRight (DescendingIndex nthArg) 
        (checkDescendingIndex f nthArg (createStCtxFromScope StCtxEmpty (arity f)) 
          (subst0 (Sub (arity f)) (sym (leftIdentity (f .arity))) subRefl) 
          (subst0 (λ scope → Term scope) (sym (leftIdentity (f .arity))) (body f)))
{-# COMPILE AGDA2HS checkTermination' #-}

checkTermination : {α : Scope Name} → SubTermContext α → NameIn defScope → Term α → Either String String
-- unfold the function to get all the arguments and build the env
checkTermination c def (TLam x body) = checkTermination (StCtxExtend x Nothing c) def body
checkTermination {α} c def body = 
  mapEitherPermissive
    (λ err → Left err)
    (λ tt → Right ("The function is terminating in its "))
    (checkTermination' (record { index = def; arity = α; body = body }))
{-# COMPILE AGDA2HS checkTermination #-}







