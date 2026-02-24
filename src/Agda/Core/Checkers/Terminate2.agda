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

checkDescendingIndexApp : (f : FunDefinition) → (nthArg : NthArg (arity f)) → (ctx : SubTermContext α) → (prf : arity f ⊆ α) → (term : Term α) → Either String (TerminatingTerm f nthArg ctx prf term)

checkDescendingIndexList f nthArg ctx prf [] = Right $ TerminatingTermListNil
checkDescendingIndexList f nthArg ctx prf (x ∷ xs) = mapEitherPermissive
                                                          (λ err → Left err)
                                                          (λ tt → mapEitherPermissive
                                                            (λ err → Left err)
                                                            (λ ttl → Right $ TerminatingTermListCons tt ttl)
                                                            (checkDescendingIndexList f nthArg ctx prf xs)
                                                          )
                                                          (checkDescendingIndex f nthArg ctx prf x)
{-# COMPILE AGDA2HS checkDescendingIndexList #-}

checkDescendingIndexApp f nthArg ctx prf (TApp func arg) = mapEitherPermissive 
                                                          (λ err → Left err) -- case where the argument is nonterminating
                                                          (λ targ → mapEitherPermissive 
                                                            (λ err →  Left err)
                                                            (λ tfunc → Right $ TerminatingApp tfunc targ) -- case where arg and func are terminating
                                                            (checkDescendingIndex f nthArg ctx prf func))
                                                          (checkDescendingIndex f nthArg ctx prf arg)
checkDescendingIndexApp f nthArg ctx prf _ = Left "Not an app" 
{-# COMPILE AGDA2HS checkDescendingIndexApp #-}

checkDescendingIndex f nthArg ctx prf (TVar x) = Right TerminatingVar
checkDescendingIndex f nthArg ctx prf (TCon c us) = Right TerminatingCon
checkDescendingIndex f nthArg ctx prf (TLam x body) = fmap TerminatingLam $ checkDescendingIndex f nthArg (StCtxExtend x Nothing ctx) (subWeaken prf) body
checkDescendingIndex f nthArg ctx prf (TApp func (TVar x)) = mapEitherPermissive 
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
checkDescendingIndex f nthArg ctx prf (TDef funcName) = case (decNamesIn funcName (index f)) of λ where
                                                          (True ⟨ p ⟩) → Left "Impossible: should have matched the App Case"
                                                          (False ⟨ p ⟩) → Right $ TerminatingDef p



checkDescendingIndex f nthArg ctx prf term = Left "Not implemented"
{-# COMPILE AGDA2HS checkDescendingIndex #-}

checkTermination : (f : FunDefinition) → Either String (Descending f)
checkTermination f = foldr helper (Left "This function is non-terminating") (iterateNthArg (arity f))
  where
    helper : NthArg (arity f) → Either String (Descending f) → Either String (Descending f)
    helper nthArg (Right res) = Right res
    helper nthArg (Left _) = 
      mapRight (DescendingIndex nthArg) 
        (checkDescendingIndex f nthArg (createStCtxFromScope StCtxEmpty (arity f)) 
          (subst0 (Sub (arity f)) (sym (leftIdentity (f .arity))) subRefl) 
          (subst0 (λ scope → Term scope) (sym (leftIdentity (f .arity))) (body f)))
{-# COMPILE AGDA2HS checkTermination #-}









