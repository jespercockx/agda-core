open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Rules.Conversion
open import Agda.Core.Reduce
open import Agda.Core.TCM.Instances

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
  (TData d pars ixs ⟨ redv ⟩) → return ((d , (pars , ixs) ⟨ redv ⟩))
  _ → tcError err
{-# COMPILE AGDA2HS reduceToData #-}

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
                ∀ {@0 d : NameData} {@0 cs : RScope (NameCon d)}
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

convCons : {{fl : Fuel}} → Singleton α →
           {d d' : NameData}
           (f : NameCon d)
           (g : NameCon d')
           (lp : TermS α (fieldScope f))
           (lq : TermS α (fieldScope g))
         → TCM (Conv (TCon f lp) (TCon g lq))
convCons r {d} {d'} f g lp lq = do
  ifDec (decNamesIn d d')
    (λ where {{refl}} → do
      ifDec (decNamesInR f g)
        (λ where {{refl}} → do
          csp ← convertTermSs r lp lq
          return $ CCon f csp)
        (tcError "constructors not convertible"))
    (tcError "constructors are from not convertible datatypes")

{-# COMPILE AGDA2HS convCons #-}

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
              → {@0 d : NameData} {@0 c : NameCon d}
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

convertEtaGeneric : ⦃ fl : Fuel ⦄ 
                    → Singleton α 
                    → (@0 x : Name) 
                    → (f : Term α)
                    → (b : Term (α ▸ x)) 
                    → TCM (b ≅ (TApp (weakenTerm _ f) (TVar (VZero x))))
convertEtaGeneric r x f b = do
  let
    subsetProof = subWeaken subRefl
    newScope    = singBind r
    term        = TApp (weakenTerm subsetProof f)
                       (TVar (VZero x))
  convertCheck newScope b term
{-# COMPILE AGDA2HS convertEtaGeneric #-}


convertWhnf : ⦃ fl : Fuel ⦄ → Singleton α → (t q : Term α) → TCM (t ≅ q)
convertWhnf r (TVar x) (TVar y) = convVars x y
convertWhnf r (TDef x) (TDef y) = convDefs x y
convertWhnf r (TData d ps is) (TData e qs ks) = convDatas r d e ps qs is ks
convertWhnf r (TCon {d = d} c lc) (TCon {d = d'} c' ld) = convCons r c c' lc ld
convertWhnf r (TLam x u) (TLam y v) = convLams r x y u v
convertWhnf r (TApp u e) (TApp v f) = convApps r u v e f
convertWhnf r (TProj u f) (TProj v g) = tcError "not implemented: conversion of projections"
convertWhnf r (TCase d ri u bs rt) (TCase d' ri' u' bs' rt') =
  convertCase r d d' ri ri' u u' bs bs' rt rt'
convertWhnf r (TPi x tu tv) (TPi y tw tz) = convPis r x y tu tw tv tz
convertWhnf r (TSort s) (TSort t) = convSorts s t
--let and ann shouldn't appear here since they get reduced away
convertWhnf r functionTerm (TLam x b) = 
  do
    conversionProof <- convertCheck newScope b term
    return (CEtaFunctions x functionTerm b conversionProof)
convertWhnf r (TLam x v) (TVar x') = tcError "implement eta-functions 2"
convertWhnf r _ _ = tcError "two terms are not the same and aren't convertible"

{-# COMPILE AGDA2HS convertWhnf #-}

convertCheck ⦃ None ⦄ r t z =
  tcError "not enough fuel to check conversion"
convertCheck ⦃ More ⦄ r t q = do
  t ⟨ tred ⟩ ← reduceTo r t
  q ⟨ qred ⟩ ← reduceTo r q
  (CRedL tred ∘ CRedR qred) <$> convertWhnf r t q

{-# COMPILE AGDA2HS convertCheck #-}

convert : Singleton α → ∀ (t q : Term α) → TCM (t ≅ q)
convert r t q = do
  I ⦃ fl ⦄ ← tcmFuel
  convertCheck r t q

{-# COMPILE AGDA2HS convert #-}
