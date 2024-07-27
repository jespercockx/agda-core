open import Haskell.Prelude as Prelude
open import Scope
open import Utils.Tactics using (auto)

open import Agda.Core.GlobalScope using (Globals; Name)
open import Agda.Core.Signature
open import Agda.Core.Syntax as Syntax
open import Agda.Core.Substitute
open import Agda.Core.Context
open import Agda.Core.Conversion
open import Agda.Core.Reduce
open import Agda.Core.TCM
open import Agda.Core.TCMInstances
open import Agda.Core.Utils

open import Haskell.Extra.Erase
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Equality

module Agda.Core.Converter
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

-- Workaround for https://github.com/agda/agda2hs/issues/324
{-# FOREIGN AGDA2HS import Agda.Core.TCMInstances #-}

private open module @0 G = Globals globals

private variable
  @0 x y : Name
  @0 α β : Scope Name

reduceTo : {@0 α : Scope Name} (r : Rezz α) (v : Term α)
         → TCM (∃[ t ∈ Term α ] (ReducesTo v t))
reduceTo r v = do
  (I {{fl}}) ← tcmFuel
  rsig ← tcmSignature
  case reduce r rsig v of λ where
    Nothing        → tcError "not enough fuel to reduce a term"
    (Just u) ⦃ p ⦄ → return $ u ⟨ ⟨ r ⟩ ⟨ rsig ⟩ it ⟨ p ⟩ ⟩
{-# COMPILE AGDA2HS reduceTo #-}

reduceToPi : {@0 α : Scope Name} (r : Rezz α)
           → (v : Term α)
           → String
           → TCM (Σ0[ x ∈ Name                        ]
                   ∃[ (a , b) ∈ Type α × Type (x ◃ α) ]
                   ReducesTo v (TPi x a b))
reduceToPi r v err = reduceTo r v >>= λ where
  (TPi x a b ⟨ redv ⟩) → return (⟨ x ⟩ ((a , b) ⟨ redv ⟩))
  _ → tcError err
{-# COMPILE AGDA2HS reduceToPi #-}

reduceToData : {@0 α : Scope Name} (r : Rezz α)
           → (v : Term α)
           → String
           → TCM (Σ0[ d ∈ Name ]
                   Σ[ dp ∈ d ∈ dataScope ]
                   ∃[ (pars , ixs) ∈ (dataParScope d ⇒ α) × (dataIxScope d ⇒ α) ]
                   ReducesTo v (TData d pars ixs))
reduceToData r v err = reduceTo r v >>= λ where
  (TData d pars ixs ⟨ redv ⟩) → return (⟨ d ⟩ (_ , (pars , ixs) ⟨ redv ⟩))
  _ → tcError err
{-# COMPILE AGDA2HS reduceToData #-}

reduceToSort : {@0 α : Scope Name} (r : Rezz α)
           → (v : Term α)
           → String
           → TCM (∃[ s ∈ Sort α ] ReducesTo v (TSort s))
reduceToSort r v err = reduceTo r v >>= λ where
  (TSort s ⟨ redv ⟩) → return (s ⟨ redv ⟩)
  _ → tcError err
{-# COMPILE AGDA2HS reduceToSort #-}

convVars : (@0 x y : Name)
           {@(tactic auto) p : x ∈ α} {@(tactic auto) q : y ∈ α}
         → TCM (Conv (TVar x) (TVar y))
convVars x y {p} {q} =
  ifDec (decIn p q)
    (λ where {{refl}} → return CRefl)
    (tcError "variables not convertible")
{-# COMPILE AGDA2HS convVars #-}

convDefs : (@0 f g : Name)
           {@(tactic auto) p : f ∈ defScope}
           {@(tactic auto) q : g ∈ defScope}
         → TCM (Conv {α = α} (TDef f) (TDef g))
convDefs f g {p} {q} =
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

convertCheck : {{fl : Fuel}} → Rezz α → (t q : Term α) → TCM (t ≅ q)
convertSubsts : {{fl : Fuel}} → Rezz α →
                (s p : β ⇒ α)
              → TCM (s ⇔ p)
convertBranches : {{fl : Fuel}} → Rezz α →
                ∀ {@0 cons : Scope Name}
                  (bs bp : Branches α cons)
                → TCM (ConvBranches bs bp)

convDatas : {{fl : Fuel}} → Rezz α →
           (@0 d e : Name)
           {@(tactic auto) dp : d ∈ dataScope}
           {@(tactic auto) ep : e ∈ dataScope}
           (ps : dataParScope d ⇒ α) (qs : dataParScope e ⇒ α)
           (is : dataIxScope d ⇒ α) (ks : dataIxScope e ⇒ α)
         → TCM (Conv (TData d ps is) (TData e qs ks))
convDatas r d e {dp} {ep} ps qs is ks = do
  ifDec (decIn dp ep)
    (λ where {{refl}} → do
      cps ← convertSubsts r ps qs
      cis ← convertSubsts r is ks
      return $ CData d cps cis)
    (tcError "datatypes not convertible")

{-# COMPILE AGDA2HS convDatas #-}

convCons : {{fl : Fuel}} → Rezz α →
           (@0 f g : Name)
           {@(tactic auto) p : f ∈ conScope}
           {@(tactic auto) q : g ∈ conScope}
           (lp : fieldScope f ⇒ α)
           (lq : fieldScope g ⇒ α)
         → TCM (Conv (TCon f lp) (TCon g lq))
convCons r f g {p} {q} lp lq = do
  ifDec (decIn p q)
    (λ where {{refl}} → do
      csp ← convertSubsts r lp lq
      return $ CCon f csp)
    (tcError "constructors not convertible")

{-# COMPILE AGDA2HS convCons #-}

convLams : {{fl : Fuel}}
         → Rezz α
         → (@0 x y : Name)
           (u : Term (x ◃ α))
           (v : Term (y ◃ α))
         → TCM (Conv (TLam x u) (TLam y v))
convLams r x y u v = do
  CLam <$> convertCheck (rezzBind r) (renameTop r u) (renameTop r v)

{-# COMPILE AGDA2HS convLams #-}

convApps : {{fl : Fuel}}
         → Rezz α
         → (u u' : Term α)
           (w w' : Term α)
         → TCM (Conv (TApp u w) (TApp u' w'))
convApps r u u' w w' = do
  cu ← convertCheck r u u'
  cw ← convertCheck r w w'
  return (CApp cu cw)

{-# COMPILE AGDA2HS convApps #-}

convertCase : {{fl : Fuel}}
            → Rezz α
            → (u u' : Term α)
            → ∀ {@0 cs cs'} (ws : Branches α cs) (ws' : Branches α cs')
            → (rt : Type (x ◃ α)) (rt' : Type (y ◃ α))
            → TCM (Conv (TCase u ws rt) (TCase u' ws' rt'))
convertCase {x = x} r u u' ws ws' rt rt' = do
  cu ← convertCheck r u u'
  cm ← convertCheck (rezzBind {x = x} r)
                       (renameTop r (unType rt))
                       (renameTop r (unType rt'))
  Erased refl ← liftMaybe (allInScope (allBranches ws) (allBranches ws'))
    "comparing case statements with different branches"
  cbs ← convertBranches r ws ws'
  return (CCase ws ws' rt rt' cu cm cbs)

{-# COMPILE AGDA2HS convertCase #-}

convPis : {{fl : Fuel}}
        → Rezz α
        → (@0 x y : Name)
          (u u' : Type α)
          (v  : Type (x ◃ α))
          (v' : Type (y ◃ α))
        → TCM (Conv (TPi x u v) (TPi y u' v'))
convPis r x y u u' v v' = do
  CPi <$> convertCheck r (unType u) (unType u')
      <*> convertCheck (rezzBind r) (unType v) (renameTop r (unType v'))

{-# COMPILE AGDA2HS convPis #-}

convertSubsts r SNil p = return CSNil
convertSubsts r (SCons x st) p =
  caseSubstBind p λ where
    y pt {{refl}} → do
      hc ← convertCheck r x y
      tc ← convertSubsts r st pt
      return (CSCons hc tc)

{-# COMPILE AGDA2HS convertSubsts #-}

convertBranch : {{fl : Fuel}}
              → Rezz α
              → ∀ {@0 con : Name}
              → (b1 b2 : Branch α con)
              → TCM (ConvBranch b1 b2)
convertBranch r (BBranch _ {cp1} rz1 rhs1) (BBranch _ {cp2} rz2 rhs2) =
  ifDec (decIn cp1 cp2)
    (λ where {{refl}} → do
      CBBranch _ cp1 rz1 rz2 rhs1 rhs2 <$>
        convertCheck (rezzCong2 _<>_ (rezzCong revScope rz1) r) rhs1 rhs2)
    (tcError "can't convert two branches that match on different constructors")

{-# COMPILE AGDA2HS convertBranch #-}

convertBranches r BsNil        bp = return CBranchesNil
convertBranches r (BsCons bsh bst) bp =
  caseBsCons bp (λ where
    bph bpt {{refl}} → CBranchesCons <$> convertBranch r bsh bph <*> convertBranches r bst bpt)

{-# COMPILE AGDA2HS convertBranches #-}

convertWhnf : {{fl : Fuel}} → Rezz α → (t q : Term α) → TCM (t ≅ q)
convertWhnf r (TVar x {xp}) (TVar y {yp}) = convVars x y
convertWhnf r (TDef x {xp}) (TDef y {yp}) = convDefs x y
convertWhnf r (TData d {dp} ps is) (TData e {ep} qs ks) = convDatas r d e ps qs is ks
convertWhnf r (TCon c {cp} lc) (TCon d {dp} ld) = convCons r c d lc ld
convertWhnf r (TLam x u) (TLam y v) = convLams r x y u v
convertWhnf r (TApp u e) (TApp v f) = convApps r u v e f
convertWhnf r (TProj u f {fp}) (TProj v g {gp}) = tcError "not implemented: conversion of projections"
convertWhnf r (TCase {cs = cs} u bs rt) (TCase {cs = cs'} u' bs' rt') =
  convertCase r u u' {cs} {cs'} bs bs' rt rt'
convertWhnf r (TPi x tu tv) (TPi y tw tz) = convPis r x y tu tw tv tz
convertWhnf r (TSort s) (TSort t) = convSorts s t
--let and ann shoudln't appear here since they get reduced away
convertWhnf r _ _ = tcError "two terms are not the same and aren't convertible"

{-# COMPILE AGDA2HS convertWhnf #-}

convertCheck {{None}} r t z =
  tcError "not enough fuel to check conversion"
convertCheck {{More}} r t q = do
  t ⟨ tred ⟩ ← reduceTo r t
  q ⟨ qred ⟩ ← reduceTo r q
  (CRedL tred ∘ CRedR qred) <$> convertWhnf r t q

{-# COMPILE AGDA2HS convertCheck #-}

convert : Rezz α → ∀ (t q : Term α) → TCM (t ≅ q)
convert r t q = do
  (I {{fl}}) ← tcmFuel
  convertCheck r t q

{-# COMPILE AGDA2HS convert #-}
