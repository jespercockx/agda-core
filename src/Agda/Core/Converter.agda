open import Haskell.Prelude as Prelude
open import Scope

open import Agda.Core.GlobalScope using (Globals; Name)
import Agda.Core.Signature as Signature

module Agda.Core.Converter
    (@0 globals : Globals)
    (open Signature globals)
    (@0 sig     : Signature)
  where

private open module @0 G = Globals globals

open import Agda.Core.Syntax globals as Syntax
open import Agda.Core.Substitute globals
open import Agda.Core.Context globals
open import Agda.Core.Conversion globals sig
open import Agda.Core.Reduce globals
open import Agda.Core.TCM globals sig
open import Agda.Core.TCMInstances
open import Agda.Core.Utils

open import Haskell.Extra.Erase
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Equality

private variable
  @0 x y : Name
  @0 α β : Scope Name


reduceTo : {@0 α : Scope Name} (r : Rezz _ α) (sig : Signature) (v : Term α) (f : Fuel)
         → TCM (∃[ t ∈ Term α ] (ReducesTo sig v t))
reduceTo r sig v f =
  case reduce r sig v f of λ where
    Nothing        → tcError "not enough fuel to reduce a term"
    (Just u) ⦃ p ⦄ → return $ u ⟨ ⟨ r ⟩ f ⟨ p ⟩ ⟩
{-# COMPILE AGDA2HS reduceTo #-}

convVars : (@0 x y : Name)
           (p : x ∈ α) (q : y ∈ α)
         → TCM (Conv (TVar x p) (TVar y q))
convVars x y p q =
  ifDec (decIn p q)
    (λ where {{refl}} → return CRefl)
    (tcError "variables not convertible")

convDefs : (@0 f g : Name)
           (p : f ∈ defScope)
           (q : g ∈ defScope)
         → TCM (Conv {α = α} (TDef f p) (TDef g q))
convDefs f g p q =
  ifDec (decIn p q)
    (λ where {{refl}} → return CRefl)
    (tcError "definitions not convertible")

convSorts : (u u' : Sort α)
          → TCM (Conv (TSort u) (TSort u'))
convSorts (STyp u) (STyp u') =
  ifDec ((u == u') ⟨ isEquality u u' ⟩)
    (λ where {{refl}} → return $ CRefl)
    (tcError "can't convert two different sorts")

convertCheck : Fuel → Rezz _ α → (t q : Term α) → TCM (t ≅ q)
convertSubsts : Fuel → Rezz _ α →
                (s p : β ⇒ α)
              → TCM (s ⇔ p)
convertBranches : Fuel → Rezz _ α →
                ∀ {@0 cons : Scope Name}
                  (bs bp : Branches α cons)
                → TCM (ConvBranches bs bp)

convCons : Fuel → Rezz _ α →
           (@0 f g : Name)
           (p : f ∈ conScope)
           (q : g ∈ conScope)
           (lp : lookupAll fieldScope p ⇒ α)
           (lq : lookupAll fieldScope q ⇒ α)
         → TCM (Conv (TCon f p lp) (TCon g q lq))
convCons fl r f g p q lp lq = do
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature
  ifDec (decIn p q)
    (λ where {{refl}} → do
      csp ← convertSubsts fl r lp lq
      return $ CCon p csp)
    (tcError "constructors not convertible")

convLams : Fuel
         → Rezz _ α
         → (@0 x y : Name)
           (u : Term (x ◃ α))
           (v : Term (y ◃ α))
         → TCM (Conv (TLam x u) (TLam y v))
convLams fl r x y u v = do
  CLam <$> convertCheck fl (rezzBind r) (renameTop r u) (renameTop r v)

convApps : Fuel
         → Rezz _ α
         → (u u' : Term α)
           (w w' : Term α)
         → TCM (Conv (TApp u w) (TApp u' w'))
convApps fl r u u' w w' = do
  cu ← convertCheck fl r u u'
  cw ← convertCheck fl r w w'
  return (CApp cu cw)

convertCase : Fuel
            → Rezz _ α
            → (u u' : Term α)
            → ∀ {@0 cs cs'} (ws : Branches α cs) (ws' : Branches α cs')
            → (rt : Type (x ◃ α)) (rt' : Type (y ◃ α))
            → TCM (Conv (TCase u ws rt) (TCase u' ws' rt'))
convertCase {x = x} fl r u u' ws ws' rt rt' = do
  cu ← convertCheck fl r u u'
  cm ← convertCheck fl (rezzBind {x = x} r)
                       (renameTop r (unType rt))
                       (renameTop r (unType rt'))
  Erased refl ← liftMaybe (allInScope (allBranches ws) (allBranches ws'))
    "comparing case statements with different branches"
  cbs ← convertBranches fl r ws ws'
  return (CCase ws ws' rt rt' cu cm cbs)

convPis : Fuel
        → Rezz _ α
        → (@0 x y : Name)
          (u u' : Type α)
          (v  : Type (x ◃ α))
          (v' : Type (y ◃ α))
        → TCM (Conv (TPi x u v) (TPi y u' v'))
convPis fl r x y u u' v v' = do
  CPi <$> convertCheck fl r (unType u) (unType u')
      <*> convertCheck fl (rezzBind r) (unType v) (renameTop r (unType v'))

convertSubsts fl r SNil p = return CSNil
convertSubsts fl r (SCons x st) p =
  caseSubstBind p λ where
    y pt {{refl}} → do
      hc ← convertCheck fl r x y
      tc ← convertSubsts fl r st pt
      return (CSCons hc tc)

convertBranch : Fuel
              → Rezz _ α
              → ∀ {@0 con : Name}
              → (b1 b2 : Branch α con)
              → TCM (ConvBranch b1 b2)
convertBranch fl r (BBranch _ cp1 rz1 rhs1) (BBranch _ cp2 rz2 rhs2) =
  ifDec (decIn cp1 cp2)
    (λ where {{refl}} → do
      CBBranch _ cp1 rz1 rz2 rhs1 rhs2 <$>
        convertCheck fl (rezzCong2 _<>_ (rezzCong revScope rz1) r) rhs1 rhs2)
    (tcError "can't convert two branches that match on different constructors")

convertBranches fl r BsNil        bp = return CBranchesNil
convertBranches fl r (BsCons bsh bst) bp =
  caseBsCons bp (λ where
    bph bpt {{refl}} → CBranchesCons <$> convertBranch fl r bsh bph <*> convertBranches fl r bst bpt)

convertCheck None r t z =
  tcError "not enough fuel to check conversion"
convertCheck (More fl) r t q = do
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  rgty ← reduceTo r sig t fuel
  rcty ← reduceTo r sig q fuel
  case (rgty Prelude., rcty) of λ where
    --for vars
    (TVar x p ⟨ rpg  ⟩ , TVar y q  ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convVars x y p q
    --for defs
    (TDef x p ⟨ rpg  ⟩ , TDef y q  ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convDefs x y p q
    --for cons
    (TCon c p lc ⟨ rpg  ⟩ , TCon d q ld ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convCons fl r c d p q lc ld
    --for lambda
    (TLam x u ⟨ rpg ⟩ , TLam y v ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convLams fl r x y u v
    --for app
    (TApp u e ⟨ rpg ⟩ , TApp v f ⟨ rpc ⟩) → do
      (CRedL rpg ∘ CRedR rpc) <$> convApps fl r u v e f
    --for proj
    (TProj u f p ⟨ rpg ⟩ , TProj v g q ⟨ rpc ⟩) → do
      tcError "not implemented: conversion of projections"
    --for case
    (TCase {cs = cs} u bs rt ⟨ rpg ⟩ , TCase {cs = cs'} u' bs' rt' ⟨ rpc ⟩) → do
      (CRedL rpg ∘ CRedR rpc) <$> convertCase fl r u u' {cs} {cs'} bs bs' rt rt'
    --for pi
    (TPi x tu tv ⟨ rpg ⟩ , TPi y tw tz ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convPis fl r x y tu tw tv tz
    --for sort
    (TSort s ⟨ rpg ⟩ , TSort t ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convSorts s t
    --let and ann shoudln't appear here since they get reduced away
    _ → tcError "two terms are not the same and aren't convertible"

convert : Rezz _ α → ∀ (t q : Term α) → TCM (t ≅ q)
convert r t q = do
  fl ← tcmFuel
  convertCheck fl r t q
