open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Rules.Conversion
open import Agda.Core.Reduce
open import Agda.Core.TCM.Instances
-- open import Agda.Core.Checkers.TypeCheck

module Agda.Core.Checkers.Converter
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

-- Workaround for https://github.com/agda/agda2hs/issues/324
{-# FOREIGN AGDA2HS import Agda.Core.TCM.Instances #-}

private open module @0 G = Globals globals

private variable
  @0 x y : Name
  @0 α β : Scope Name
  @0 rβ : RScope Name

reduceTo : {@0 α : Scope Name} (r : Singleton α) (v : Term α)
         → TCM (∃[ t ∈ Term α ] (ReducesTo v t))
reduceTo r v = do
  (I {{fl}}) ← tcmFuel
  rsig ← tcmSignature
  case reduce r rsig v of λ where
    Nothing        → tcError "not enough fuel to reduce a term"
    (Just u) ⦃ p ⦄ → return $ u ⟨ ⟨ r ⟩ ⟨ rsig ⟩ it ⟨ p ⟩ ⟩
{-# COMPILE AGDA2HS reduceTo #-}

reduceToPi : {@0 α : Scope Name} (r : Singleton α)
           → (v : Term α)
           → String
           → TCM (Σ0[ x ∈ Name                        ]
                   ∃[ (a , b) ∈ Type α × Type  (α ▸ x) ]
                   ReducesTo v (TPi x a b))
reduceToPi r v err = reduceTo r v >>= λ where
  (TPi x a b ⟨ redv ⟩) → return (⟨ x ⟩ ((a , b) ⟨ redv ⟩))
  _ → tcError err
{-# COMPILE AGDA2HS reduceToPi #-}

reduceToData : {@0 α : Scope Name} (r : Singleton α)
           → (v : Term α)
           → String
           → TCM (Σ[ d ∈ NameIn dataScope ]
                  ∃[ (pars , ixs) ∈ (TermS α (dataParScope d)) × (TermS α (dataIxScope d)) ]
                  ReducesTo v (TData d pars ixs))
reduceToData r v err = reduceTo r v >>= λ where
  (TData d pars ixs ⟨ redv ⟩) → return (d , (pars , ixs) ⟨ redv ⟩)
  _ → tcError err
{-# COMPILE AGDA2HS reduceToData #-}

reduceToRec : {@0 α : Scope Name} (r : Singleton α)
          → (v : Term α)
          → String
          → TCM (Σ[ rn ∈ NameIn recScope ]
                 ∃[ pars ∈ TermS α (recParScope rn) ]
                 ReducesTo v (TRec rn pars))
reduceToRec r v err = reduceTo r v >>= λ where
  (TRec rn pars ⟨ redv ⟩) → return (rn , pars ⟨ redv ⟩)
  _ → tcError err
{-# COMPILE AGDA2HS reduceToRec #-}

reduceToTRecCon : {@0 α : Scope Name} (r : Singleton α)
          → (v : Term α)
          → String
          → TCM (Σ[ rn ∈ NameIn recScope ]
                 ∃[ args ∈ TermS α (recFieldScope rn)]
                 ReducesTo v (TRecCon rn args))
reduceToTRecCon r v err = reduceTo r v >>= λ where
  (TRecCon rn args ⟨ redv ⟩) → return (rn , (args ⟨ redv ⟩))
  _ → tcError err
{-# COMPILE AGDA2HS reduceToTRecCon #-}

reduceToSort : {@0 α : Scope Name} (r : Singleton α)
           → (v : Term α)
           → String
           → TCM (∃[ s ∈ Sort α ] ReducesTo v (TSort s))
reduceToSort r v err = reduceTo r v >>= λ where
  (TSort s ⟨ redv ⟩) → return (s ⟨ redv ⟩)
  _ → tcError err
{-# COMPILE AGDA2HS reduceToSort #-}



convNamesIn : (x y : NameIn α) → TCM (Erase (x ≡ y))
convNamesIn x y =
  ifEqualNamesIn x y
    (λ where {{refl}} → return (Erased refl))
    (tcError "names not equal")
{-# COMPILE AGDA2HS convNamesIn #-}

convNamesInR : (x y : NameInR rβ) → TCM (Erase (x ≡ y))
convNamesInR x y = 
  ifEqualNamesInR x y 
    (λ where {{refl}} → return (Erased refl))
    (tcError "names not equal")
{-# COMPILE AGDA2HS convNamesInR #-}

convVars : (x y : NameIn α)
         → TCM (Conv (TVar x) (TVar y))
convVars x y = do
  Erased refl ← convNamesIn x y
  return CRefl
{-# COMPILE AGDA2HS convVars #-}

convDefs : (f g : NameIn defScope)
         → TCM (Conv {α = α} (TDef f) (TDef g))
convDefs (⟨ f ⟩ p) (⟨ g ⟩ q) =
  ifDec (decIn p q)
    (λ where {{refl}} → return CRefl)
    (tcError "definitions not convertible")
{-# COMPILE AGDA2HS convDefs #-}

convSorts : (u u' : Sort α)
          → TCM (Conv (TSort u) (TSort u'))
convSorts (STyp u) (STyp u') =
  ifDec ((u == u') ⟨ isEquality u u' ⟩)
    (λ where {{refl}} → return $ CRefl)
    (tcError "can't convert two different sorts")
{-# COMPILE AGDA2HS convSorts #-}

convertCheck : {{fl : Fuel}} → Singleton α → (t q : Term α) → TCM (t ≅ q)
convertTermSs : {{fl : Fuel}} → Singleton α →
                (s p : TermS α rβ)
              → TCM (s ⇔ p)
convertBranches : {{fl : Fuel}} → Singleton α →
                ∀ {@0 d : NameData} {@0 cs : RScope (NameDataCon d)}
                  (bs bp : Branches α d cs)
                → TCM (ConvBranches bs bp)

convDatas : {{fl : Fuel}} → Singleton α →
           (d e : NameData)
           (ps : TermS α (dataParScope d)) (qs : TermS α (dataParScope e))
           (is : TermS α (dataIxScope d)) (ks : TermS α (dataIxScope e))
         → TCM (Conv (TData d ps is) (TData e qs ks))
convDatas r d e ps qs is ks = do
  ifDec (decIn (proj₂ d) (proj₂ e))
    (λ where {{refl}} → do
      cps ← convertTermSs r ps qs
      cis ← convertTermSs r is ks
      return $ CData d cps cis)
    (tcError "datatypes not convertible")

{-# COMPILE AGDA2HS convDatas #-}

convRecs : {{fl : Fuel}} → Singleton α → (rn1 rn2 : NameRec)
            (pars1 : TermS α (recParScope rn1)) (pars2 : TermS α (recParScope rn2))
          → TCM (Conv (TRec rn1 pars1) (TRec rn2 pars2))
convRecs r rn1 rn2 pars1 pars2 = do
  ifDec (decIn (proj₂ rn1) (proj₂ rn2))
    (λ where {{refl}} → do
      cps ← convertTermSs r pars1 pars2
      return $ (CRec rn1 pars1 pars2 cps)
    )
    (tcError "record types not convertible")
{-# COMPILE AGDA2HS convRecs #-}

convDataCons : {{fl : Fuel}} → Singleton α →
           {d d' : NameData}
           (f : NameDataCon d)
           (g : NameDataCon d')
           (lp : TermS α (dataFieldScope f))
           (lq : TermS α (dataFieldScope g))
         → TCM (Conv (TDataCon f lp) (TDataCon g lq))
convDataCons r {d} {d'} f g lp lq = do
  ifDec (decNamesIn d d')
    (λ where {{refl}} → do
      ifDec (decNamesInR f g)
        (λ where {{refl}} → do
          csp ← convertTermSs r lp lq
          return $ CDataCon f csp)
        (tcError "constructors not convertible"))
    (tcError "constructors are from not convertible datatypes")

{-# COMPILE AGDA2HS convDataCons #-}

convRecCons : {{fl : Fuel}} → Singleton α → 
          (rn1 : NameRec)
          (rn2 : NameRec)
          (args1 : TermS α (recFieldScope rn1))
          (args2 : TermS α (recFieldScope rn2))
        → TCM (Conv (TRecCon rn1 args1) (TRecCon rn2 args2))
convRecCons r rn1 rn2 args1 args2 = do 
  ifDec (decNamesIn rn1 rn2) 
    (λ where {{refl}} → do
      csp ← convertTermSs r args1 args2
      return $ CRecCon rn1 csp
    ) 
    (tcError "record constructors are from non-convertible record types")
{-# COMPILE AGDA2HS convRecCons #-}

convLams : {{fl : Fuel}}
         → Singleton α
         → (@0 x y : Name)
           (u : Term  (α ▸ x))
           (v : Term  (α ▸ y))
         → TCM (Conv (TLam x u) (TLam y v))
convLams r x y u v = do
  CLam <$> convertCheck (singBind r) (renameTop r u) (renameTop r v)

{-# COMPILE AGDA2HS convLams #-}

convApps : {{fl : Fuel}}
         → Singleton α
         → (u u' : Term α)
           (w w' : Term α)
         → TCM (Conv (TApp u w) (TApp u' w'))
convApps r u u' w w' = do
  cu ← convertCheck r u u'
  cw ← convertCheck r w w'
  return (CApp cu cw)

{-# COMPILE AGDA2HS convApps #-}

convProjs : {{fl : Fuel}}
          → Singleton α
          → (rn1 rn2 : NameRec)
          → (recTerm1 recTerm2 : Term α)
          → (f : NameProj rn1)
          → (g : NameProj rn2)
          → TCM (Conv (TProj recTerm1 f) (TProj recTerm2 g))
convProjs r rn1 rn2 recTerm1 recTerm2 f g = do
  ifDec (decNamesIn rn1 rn2)
    (λ where {{refl}} → do
      Erased refl ← convNamesInR f g
      crecTerm ← convertCheck r recTerm1 recTerm2 
      return (CProj crecTerm)
    )
    (tcError "projections not convertible")

{-# COMPILE AGDA2HS convProjs #-} 

convertCase : {{fl : Fuel}}
            → Singleton α
            → (d d' : NameData)
            → (r : Singleton (dataIxScope d)) (r' : Singleton (dataIxScope d'))
            → (u u' : Term α)
            → ∀ (ws : Branches α d (AllNameCon d)) (ws' : Branches α d' (AllNameCon d'))
            → (rt : Type (_ ▸ x)) (rt' : Type (_ ▸ y))
            → TCM (Conv (TCase d r u ws rt) (TCase d' r' u' ws' rt'))
convertCase {x = x} rα d d' ri ri' u u' ws ws' rt rt' = do
  Erased refl ← convNamesIn d d'
  cu ← convertCheck rα u u'
  let r  = singExtScope rα ri
      r' = singExtScope rα ri'
  cm ← convertCheck (singBind {x = x} r)
                    (renameTop r (unType rt))
                    (renameTop r' (unType rt'))
  cbs ← convertBranches rα ws ws'
  return (CCase d ri ri' ws ws' rt rt' cu cm cbs)

{-# COMPILE AGDA2HS convertCase #-}

convPis : {{fl : Fuel}}
        → Singleton α
        → (@0 x y : Name)
          (u u' : Type α)
          (v  : Type  (α ▸ x))
          (v' : Type  (α ▸ y))
        → TCM (Conv (TPi x u v) (TPi y u' v'))
convPis r x y u u' v v' =
  CPi <$> convertCheck r (unType u) (unType u')
      <*> convertCheck (singBind r) (unType v) (renameTop r (unType v'))

{-# COMPILE AGDA2HS convPis #-}

convertTermSs r ⌈⌉ _ = return CSNil
convertTermSs r (x ↦ u ◂ s0) t =
  caseTermSCons t (λ where v t0 ⦃ refl ⦄ → do
      hc ← convertCheck r u v
      tc ← convertTermSs r s0 t0
      return (CSCons hc tc))

{-# COMPILE AGDA2HS convertTermSs #-}

convertBranch : ⦃ fl : Fuel ⦄
              → Singleton α
              → {@0 d : NameData} {@0 c : NameDataCon d}
              → (b1 : Branch α c) (b2 : Branch α c)
              → TCM (ConvBranch b1 b2)
convertBranch r (BBranch rc rz1 rhs1) (BBranch rc' rz2 rhs2) =
      CBBranch rc rc' rz1 rz2 rhs1 rhs2 <$>
        convertCheck (singExtScope r rz2) rhs1 rhs2
{-# COMPILE AGDA2HS convertBranch #-}

convertBranches r BsNil            bp = return CBranchesNil
convertBranches r (BsCons bsh bst) bp =
  caseBsCons bp (λ where bph bpt ⦃ refl ⦄ →
                          CBranchesCons <$> convertBranch r bsh bph <*> convertBranches r bst bpt)
{-# COMPILE AGDA2HS convertBranches #-}

-- Returns a proof a body `b` of a function is convertible into the term `(f x)` 
-- Used in both cases of untyped eta-conversion for functions
convertEtaFuncsHelper : ⦃ fl : Fuel ⦄ 
                    → Singleton α 
                    → (@0 x : Name) 
                    → (f : Term α)
                    → (b : Term (α ▸ x)) 
                    → TCM (b ≅ (TApp (weakenTerm _ f) (TVar (VZero x))))
convertEtaFuncsHelper r x f b = do
  let
    subsetProof = subWeaken subRefl
    newScope    = singBind r
    term        = TApp (weakenTerm subsetProof f)
                       (TVar (VZero x))
  convertCheck newScope b term
{-# COMPILE AGDA2HS convertEtaFuncsHelper #-}

-- Returns a proof that the termS `argsTermS` is convertible into the termS `[fst p ; snd p ; ... nth p]`
-- Used in both cases of untyped eta-conversion for records
convertEtaRecsHelper : ⦃ fl : Fuel ⦄
                    → {rn : NameRec}
                    → Singleton α
                    → (rt : Term α)
                    → (argsTermS : TermS α (recFieldScope rn))
                    → TCM (argsTermS ⇔ (etaProjTermS (singTermS argsTermS) ((TProj {rn = rn} rt))))
convertEtaRecsHelper {rn = rn} r rt argsTermS = 
  convertTermSs r argsTermS (etaProjTermS (singTermS argsTermS) ((TProj {rn = rn} rt)))
{-# COMPILE AGDA2HS convertEtaRecsHelper #-}

checkNonEmptyHelper : {@0 rscope : RScope Name} 
  → (singScope : Singleton rscope)
  → (∃ Nat (λ n → lengthOfRScope singScope ≡ n))
  → TCM (∃ Nat (λ n' → lengthOfRScope singScope ≡ suc n'))
checkNonEmptyHelper a (zero ⟨ proof₁ ⟩) = tcError "Cannot apply untyped eta-conversion 
  for records on a record whose 
  constructor takes zero arguments"
checkNonEmptyHelper a (suc value₁ ⟨ proof₁ ⟩) = return (value₁ ⟨ proof₁ ⟩)  
{-# COMPILE AGDA2HS checkNonEmptyHelper #-}


checkNonEmpty : {@0 rscope : RScope Name} →
  (singScope : Singleton rscope) →
  TCM (∃ Nat (λ n → lengthOfRScope singScope ≡ suc n))
checkNonEmpty singScope = checkNonEmptyHelper singScope ((lengthOfRScope singScope) ⟨ refl ⟩)
{-# COMPILE AGDA2HS checkNonEmpty #-}
             

convertTerms : ⦃ fl : Fuel ⦄ → Singleton α → (t q : Term α) → TCM (t ≅ q)
convertTerms r (TVar x) (TVar y) = convVars x y
convertTerms r (TDef x) (TDef y) = convDefs x y
convertTerms r (TData d ps is) (TData e qs ks) = convDatas r d e ps qs is ks
convertTerms r (TRec rn1 pars1) (TRec rn2 pars2) = convRecs r rn1 rn2 pars1 pars2
convertTerms r (TDataCon {d = d} c lc) (TDataCon {d = d'} c' ld) = convDataCons r c c' lc ld
convertTerms r (TRecCon rn1 args1) (TRecCon rn2 args2) = convRecCons r rn1 rn2 args1 args2
convertTerms r (TLam x u) (TLam y v) = convLams r x y u v
convertTerms r (TApp u e) (TApp v f) = convApps r u v e f
convertTerms r (TProj {rn = rn1} recTerm1 f) (TProj {rn = rn2} recTerm2 g) = convProjs r rn1 rn2 recTerm1 recTerm2 f g
convertTerms r (TCase d ri u bs rt) (TCase d' ri' u' bs' rt') =
  convertCase r d d' ri ri' u u' bs bs' rt rt'
convertTerms r (TPi x tu tv) (TPi y tw tz) = convPis r x y tu tw tv tz
convertTerms r (TSort s) (TSort t) = convSorts s t
--let and ann shouldn't appear here since they get reduced away
convertTerms r functionTerm (TLam x b) = 
  do
    conversionProof <- convertEtaFuncsHelper r x functionTerm b
    return (CEtaFunctionsLeft x functionTerm b conversionProof)
convertTerms r (TLam x b) functionTerm = 
  do
    conversionProof <- convertEtaFuncsHelper r x functionTerm b
    return (CEtaFunctionsRight x functionTerm b conversionProof)
convertTerms r recTerm (TRecCon rn argsTermS) = do
    let singScope = singTermS argsTermS
    proofNonEmpty ← checkNonEmpty singScope
    convProof ← convertEtaRecsHelper r recTerm argsTermS
    return (CEtaRecordsLeft rn recTerm argsTermS singScope proofNonEmpty convProof)
convertTerms r (TRecCon rn argsTermS) recTerm = do
    let singScope = singTermS argsTermS
    proofNonEmpty ← checkNonEmpty singScope
    convProof ← convertEtaRecsHelper r recTerm argsTermS
    return (CEtaRecordsRight rn recTerm argsTermS singScope proofNonEmpty convProof)
convertTerms r _ _ = tcError "two terms are not the same and aren't convertible"

{-# COMPILE AGDA2HS convertTerms #-}

convertCheck ⦃ None ⦄ r t z =
  tcError "not enough fuel to check conversion"
convertCheck ⦃ More ⦄ r t q = do
  t ⟨ tred ⟩ ← reduceTo r t
  q ⟨ qred ⟩ ← reduceTo r q
  (CRedL tred ∘ CRedR qred) <$> convertTerms r t q

{-# COMPILE AGDA2HS convertCheck #-}

convert : Singleton α → ∀ (t q : Term α) → TCM (t ≅ q)
convert r t q = do
  I ⦃ fl ⦄ ← tcmFuel
  convertCheck r t q

{-# COMPILE AGDA2HS convert #-}
