{-# OPTIONS --allow-unsolved-metas #-}
open import Haskell.Prelude

open import Scope

open import Agda.Core.GlobalScope using (Globals)
import Agda.Core.Signature as Signature

module Agda.Core.Converter
    {@0 name    : Set}
    (@0 globals : Globals name)
    (open Signature globals)
    (@0 sig     : Signature)
  where  

private open module @0 G = Globals globals

open import Agda.Core.Syntax globals as Syntax
open import Agda.Core.Context globals
open import Agda.Core.Conversion globals sig
open import Agda.Core.Reduce globals
open import Agda.Core.TCM globals sig
open import Agda.Core.Utils hiding (_,_)

open import Haskell.Extra.Erase
open import Haskell.Extra.Dec
open import Haskell.Law.Eq

private variable
  @0 α : Scope name

convVars : ∀ Γ
           (s : Term α)
           (@0 x y : name)
           (p : x ∈ α) (q : y ∈ α)
         → TCM (Conv Γ s (TVar x p) (TVar y q))
convVars ctx _ x y p q =
  ifDec (decIn p q)
    (λ where {{refl}} → return CRefl)
    (tcError "variables not convertible")

convDefs : ∀ Γ
           (s : Term α)
           (@0 f g : name)
           (p : f ∈ defScope)
           (q : g ∈ defScope)
         → TCM (Conv {α = α} Γ s (TDef f p) (TDef g q))
convDefs ctx s f g p q =
  ifDec (decIn p q)
    (λ where {{refl}} → return CRefl)
    (tcError "definitions not convertible")

convSorts : ∀ Γ
            (s : Term α)
            (u u' : Sort α)
          → TCM (Conv {α = α} Γ s (TSort u) (TSort u'))
convSorts ctx s (STyp u) (STyp u') =
  ifDec ((u == u') ⟨ isEquality u u' ⟩)
    (λ where {{refl}} → return $ CRefl)
    (tcError "can't convert two different sorts")

{-# TERMINATING #-}
convert : ∀ Γ (ty : Term α) (t q : Term α) → TCM (Γ ⊢ t ≅ q ∶ ty)
convertElims : ∀ Γ
               (ty : Term α)
               (u : Term α)
               (w z : Elim α)
             → TCM (Γ ⊢ u [ w ≅ z ] ∶ ty)

convCons : ∀ Γ
           (s : Term α)
           (@0 f g : name)
           (p : f ∈ conScope)
           (q : g ∈ conScope)
           (lp : lookupAll fieldScope p ⇒ α)
           (lq : lookupAll fieldScope q ⇒ α)
         → TCM (Conv {α = α} Γ s (TCon f p lp) (TCon g q lq))
convCons {α = α} ctx s f g p q lp lq =
  ifDec (decIn p q)
    (λ where {{refl}} → {!!})
    (tcError "constructors not convertible")

convLams : ∀ Γ
           (s : Term α)
           (@0 x y : name)
           (u : Term (x ◃ α))
           (v : Term (y ◃ α))
         → TCM (Conv {α = α} Γ s (TLam x u) (TLam y v))
convLams ctx (TPi z a b) x y u v = do
  let r = rezzScope ctx
  CLam <$> convert (ctx , z ∶ a) (unType b) (renameTop r u) (renameTop r v)
convLams ctx ty x y u v = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  (TPi z a b) ⟨ rp ⟩  ← reduceTo r sig ty fuel
    where
      _ → tcError "can't convert two terms when the type doesn't reduce to a Pi"
  CRedT rp <$> CLam <$>
    convert (ctx , z ∶ a) (unType b) (renameTop r u) (renameTop r v)

convApps : ∀ Γ
           (s : Term α)
           (u u' : Term α)
           (w w' : Elim α)
         → TCM (Conv {α = α} Γ s (TApp u w) (TApp u' w'))
convApps ctx s u u' w w' =
  CApp <$> convert ctx {!!} u u'
       <*> convertElims ctx s u w w'

convPis : ∀ Γ
          (s : Term α)
          (@0 x y : name)
          (u u' : Type α)
          (v  : Type (x ◃ α))
          (v' : Type (y ◃ α))
        → TCM (Conv {α = α} Γ s (TPi x u v) (TPi y u' v'))
convPis ctx (TSort s) x y u u' v v' = {!!}
--TODO should be CRedT after we reduce the type ty and figure out if it's a sort
convPis ctx _         x y u u' v v' = {!!}


convertElims ctx (TPi x a b) u (EArg w) (EArg w') =
  CEArg <$> convert ctx (unType a) w w'
convertElims ctx ty u (EArg w) (EArg w') = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature
  (TPi x a b) ⟨ rp ⟩  ← reduceTo r sig ty fuel
    where
      _ → tcError "can't convert two terms when the type doesn't reduce to a Pi"
  CERedT rp <$> CEArg <$> convert ctx (unType a) w w'
convertElims ctx ty u w w' = tcError "can't convert two elims"

convert ctx ty t q = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  rgty ← reduceTo r sig t fuel
  rcty ← reduceTo r sig q fuel
  case (rgty , rcty) of λ where
    --for vars
    (TVar x p ⟨ rpg  ⟩ , TVar y q  ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convVars ctx ty x y p q
    --for defs
    (TDef x p ⟨ rpg  ⟩ , TDef y q  ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convDefs ctx ty x y p q
    --for cons
    (TCon c p lc ⟨ rpg  ⟩ , TCon d q ld ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convCons ctx ty c d p q lc ld
    --for lambda
    (TLam x u ⟨ rpg ⟩ , TLam y v ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convLams ctx ty x y u v
    --for app
    (TApp u e ⟨ rpg ⟩ , TApp v f ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convApps ctx ty u v e f
    --for pi
    (TPi x tu tv ⟨ rpg ⟩ , TPi y tw tz ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convPis ctx ty x y tu tw tv tz
    --for sort
    (TSort s ⟨ rpg ⟩ , TSort t ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convSorts ctx ty s t
    _ → tcError "sorry"
