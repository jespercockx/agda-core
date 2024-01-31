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
open import Agda.Core.Substitute globals
open import Agda.Core.Context globals
open import Agda.Core.Conversion globals sig
open import Agda.Core.Reduce globals
open import Agda.Core.TCM globals sig
open import Agda.Core.Utils renaming (_,_ to _Σ,_)

open import Haskell.Extra.Erase
open import Haskell.Extra.Dec
open import Haskell.Law.Eq

private variable
  @0 α : Scope name

convVars : ∀ Γ
           (s : Term α)
           (@0 x y : name)
           (p : x ∈ α) (q : y ∈ α)
         → TCM (Conv Γ (TVar x p) (TVar y q))
convVars ctx _ x y p q =
  ifDec (decIn p q)
    (λ where {{refl}} → return CRefl)
    (tcError "variables not convertible")

convVarsI : ∀ Γ
            (@0 x y : name)
            (p : x ∈ α) (q : y ∈ α)
          → TCM (Σ[ ty ∈ Term α ] (Γ ⊢ (TVar x p) ≅ (TVar y q)))
convVarsI ctx x y p q =
  ifDec (decIn p q)
    (λ where {{refl}} → return $ (unType $ lookupVar ctx x p) Σ, CRefl)
    (tcError "variables not convertible")

convDefs : ∀ Γ
           (s : Term α)
           (@0 f g : name)
           (p : f ∈ defScope)
           (q : g ∈ defScope)
         → TCM (Conv {α = α} Γ (TDef f p) (TDef g q))
convDefs ctx s f g p q =
  ifDec (decIn p q)
    (λ where {{refl}} → return CRefl)
    (tcError "definitions not convertible")

convDefsI : ∀ Γ
            (@0 f g : name)
            (p : f ∈ defScope)
            (q : g ∈ defScope)
          → TCM (Σ[ ty ∈ Term α ] (Conv {α = α} Γ (TDef f p) (TDef g q)))
convDefsI ctx f g p q = do
  rezz sig ← tcmSignature
  let ty = unType $ weakenType subEmpty $ getType sig f p
  ifDec (decIn p q)
    (λ where {{refl}} → return $ ty Σ, CRefl)
    (tcError "definitions not convertible")

convSorts : ∀ Γ
            (s : Term α)
            (u u' : Sort α)
          → TCM (Conv {α = α} Γ (TSort u) (TSort u'))
convSorts ctx s (STyp u) (STyp u') =
  ifDec ((u == u') ⟨ isEquality u u' ⟩)
    (λ where {{refl}} → return $ CRefl)
    (tcError "can't convert two different sorts")

convSortsI : ∀ Γ
             (u u' : Sort α)
           → TCM (Σ[ ty ∈ Term α ] (Conv {α = α} Γ (TSort u) (TSort u')))
convSortsI ctx (STyp u) (STyp u') =
  ifDec ((u == u') ⟨ isEquality u u' ⟩)
    (λ where {{refl}} → return $ (TSort $ sucSort $ STyp u) Σ, CRefl)
    (tcError "can't convert two different sorts")

{-# TERMINATING #-}
convertCheck : ∀ Γ (ty : Term α) (t q : Term α) → TCM (Γ ⊢ t ≅ q)
convertInfer : ∀ Γ (t q : Term α) → TCM (Σ (Term α) (λ ty → Γ ⊢ t ≅ q))
convertElims : ∀ Γ
                 (s : Term α)
                 (u : Term α)
                 (v v' : Elim α)
             → TCM (Σ ((Elim α → Term α) → Term α) (λ f → Γ ⊢ v ≃ v'))
convertSubsts : ∀ {@0 α β} Γ → (ty : Telescope α β) → (s p : β ⇒ α) → TCM (Γ ⊢ s ⇔ p)

convCons : ∀ Γ
           (s : Term α)
           (@0 f g : name)
           (p : f ∈ conScope)
           (q : g ∈ conScope)
           (lp : lookupAll fieldScope p ⇒ α)
           (lq : lookupAll fieldScope q ⇒ α)
         → TCM (Conv {α = α} Γ (TCon f p lp) (TCon g q lq))
convCons {α = α} ctx s f g p q lp lq = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature
  (TDef d dp) ⟨ rp ⟩  ← reduceTo r sig s fuel
    where
      _ → tcError "can't convert two constructors when their type isn't a definition"
  ifDec (decIn p q)
    (λ where {{refl}} → do
      (DatatypeDef df) ← return $ getDefinition sig d dp
        where
          _ → tcError "can't convert two constructors when their type isn't a datatype"
      con ← liftMaybe (getConstructor f p df) "can't find a constructor with such a name"
      csp ← convertSubsts ctx {!!} lp lq
      return $ CCon p csp)
    (tcError "constructors not convertible")

convLams : ∀ Γ
           (s : Term α)
           (@0 x y : name)
           (u : Term (x ◃ α))
           (v : Term (y ◃ α))
         → TCM (Conv {α = α} Γ (TLam x u) (TLam y v))
convLams ctx (TPi z a b) x y u v = do
  let r = rezzScope ctx
  CLam <$> convertCheck (ctx , z ∶ a) (unType b) (renameTop r u) (renameTop r v)
convLams ctx ty x y u v = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  (TPi z a b) ⟨ rp ⟩  ← reduceTo r sig ty fuel
    where
      _ → tcError "can't convert two terms when the type doesn't reduce to a Pi"
  CLam <$> convertCheck (ctx , z ∶ a) (unType b) (renameTop r u) (renameTop r v)

convAppsI : ∀ Γ
            (u u' : Term α)
            (w w' : Elim α)
          → TCM (Σ[ ty ∈ Term α ] (Conv {α = α} Γ (TApp u w) (TApp u' w')))
convAppsI ctx u u' w w' = do
  su Σ, cu ← convertInfer ctx u u'
  f Σ, cv  ← convertElims ctx su u w w'
  return $ (f $ TApp u) Σ, CApp cu cv

convPis : ∀ Γ
          (s : Term α)
          (@0 x y : name)
          (u u' : Type α)
          (v  : Type (x ◃ α))
          (v' : Type (y ◃ α))
        → TCM (Conv {α = α} Γ (TPi x u v) (TPi y u' v'))
convPis ctx (TSort s) x y u u' v v' = do
  let r = rezzScope ctx

  CPi <$> convertCheck ctx (TSort $ typeSort u) (unType u) (unType u')
      <*> convertCheck (ctx , x ∶ u) (TSort $ typeSort v) (unType v) (renameTop r (unType v'))
convPis ctx t x y u u' v v' = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  (TSort s) ⟨ rp ⟩  ← reduceTo r sig t fuel
    where
      _ → tcError "can't convert two terms when the type does not reduce to a sort"
  cu ← convertCheck ctx (TSort $ typeSort u) (unType u) (unType u')
  cv ← convertCheck (ctx , x ∶ u) (TSort $ typeSort v) (unType v) (renameTop r (unType v'))
  return $ CPi cu cv

convertElims ctx (TPi x a b) u (EArg w) (EArg w') = do
  let r = rezzScope ctx
      ksort = piSort (typeSort a) (typeSort b)
  cw ← convertCheck ctx (unType a) w w'
  return $ (λ _ → substTop r w (unType b)) Σ, CEArg cw
convertElims ctx t u (EArg w) (EArg w') = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  (TPi x a b) ⟨ rp ⟩  ← reduceTo r sig t fuel
    where
      _ → tcError "can't convert two terms when the type does not reduce to a Pi type"
  let ksort = piSort (typeSort a) (typeSort b)
  cw ← convertCheck ctx (unType a) w w'
  return $ (λ _ → substTop r w (unType b)) Σ, CEArg cw
convertElims ctx s u w w' = tcError "not implemented yet"

convertSubsts ctx tel SNil p = return CSNil
convertSubsts ctx tel (SCons x st) p =
  caseSubstBind (λ ss → TCM (ctx ⊢ (SCons x st) ⇔ ss)) p $ λ y pt →
  caseTelBind _ tel $ λ a tel → do
    let r = rezzScope ctx
    hc ← convertCheck ctx (unType a) x y
    tc ← convertSubsts ctx (substTelescope (SCons x (idSubst r)) tel) st pt
    return $ CSCons hc tc

convertCheck ctx ty t q = do
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
    (TApp u e ⟨ rpg ⟩ , TApp v f ⟨ rpc ⟩) → do
      snd <$> map2 (CRedL rpg ∘ CRedR rpc) <$> convAppsI ctx u v e f
    --for pi
    (TPi x tu tv ⟨ rpg ⟩ , TPi y tw tz ⟨ rpc ⟩) → 
      CRedL rpg <$> CRedR rpc <$> convPis ctx ty x y tu tw tv tz
    --for sort
    (TSort s ⟨ rpg ⟩ , TSort t ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convSorts ctx ty s t
    _ → tcError "sorry"

convertInfer ctx t q = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  rgty ← reduceTo r sig t fuel
  rcty ← reduceTo r sig q fuel
  case (rgty , rcty) of λ where
    --for vars
    (TVar x p ⟨ rpg  ⟩ , TVar y q ⟨ rpc ⟩) →
      map2 (CRedL rpg ∘ CRedR rpc) <$> convVarsI ctx x y p q
    --for defs
    (TDef x p ⟨ rpg  ⟩ , TDef y q  ⟨ rpc ⟩) →
      map2 (CRedL rpg ∘ CRedR rpc) <$> convDefsI ctx x y p q
    --for cons
    (TCon c p lc ⟨ rpg  ⟩ , TCon d q ld ⟨ rpc ⟩) →
      tcError "non implemented yet"
    --for lambda
    (TLam x u ⟨ rpg ⟩ , TLam y v ⟨ rpc ⟩) →
      tcError "non inferrable"
    --for app
    (TApp u e ⟨ rpg ⟩ , TApp v f ⟨ rpc ⟩) →
      map2 (CRedL rpg ∘ CRedR rpc) <$> convAppsI ctx u v e f
    --for pi
    (TPi x tu tv ⟨ rpg ⟩ , TPi y tw tz ⟨ rpc ⟩) →
      tcError "non implemented yet"
    --for sort
    (TSort s ⟨ rpg ⟩ , TSort t ⟨ rpc ⟩) →
      map2 (CRedL rpg ∘ CRedR rpc) <$> convSortsI ctx s t
    _ → tcError "sorry"


convert : ∀ Γ (ty : Term α) (t q : Term α) → TCM (Γ ⊢ t ≅ q)
convert = convertCheck
