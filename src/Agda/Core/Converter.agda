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
open import Agda.Core.TCMInstances
open import Agda.Core.Utils renaming (_,_ to _Σ,_)

open import Haskell.Extra.Erase
open import Haskell.Extra.Dec
open import Haskell.Law.Eq
open import Haskell.Law.Equality

private variable
  @0 α : Scope name


reduceTo : {@0 α : Scope name} (r : Rezz _ α) (sig : Signature) (v : Term α) (f : Fuel)
         → TCM (∃[ t ∈ Term α ] (ReducesTo sig v t))
reduceTo r sig v f =
  case reduce r sig v f of λ where
    Nothing        → tcError "not enough fuel to reduce a term"
    (Just u) ⦃ p ⦄ → return $ u ⟨ ⟨ r ⟩ f ⟨ p ⟩ ⟩
{-# COMPILE AGDA2HS reduceTo #-}


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

convertCheck : Fuel → ∀ Γ (ty : Term α) (t q : Term α) → TCM (Γ ⊢ t ≅ q)
convertInfer : Fuel → ∀ Γ (t q : Term α) → TCM (Σ (Term α) (λ ty → Γ ⊢ t ≅ q))
convertElims : Fuel
             → ∀ Γ
                (s : Term α)
                (u : Term α)
                (v v' : Elim α)
             → TCM (Σ ((Elim α → Term α) → Term α) (λ f → Γ ⊢ v ≃ v'))
convertSubsts : Fuel
              → ∀ {@0 α β} Γ
                  (ty : Telescope α β)
                  (s p : β ⇒ α)
              → TCM (Γ ⊢ s ⇔ p)

convCons : Fuel →
           ∀ Γ
           (s : Term α)
           (@0 f g : name)
           (p : f ∈ conScope)
           (q : g ∈ conScope)
           (lp : lookupAll fieldScope p ⇒ α)
           (lq : lookupAll fieldScope q ⇒ α)
         → TCM (Conv {α = α} Γ (TCon f p lp) (TCon g q lq))
convCons         None      ctx s f g p q lp lq =
  tcError "not enough fuel to convert two constructors"
convCons {α = α} (More fl) ctx s f g p q lp lq = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature
  let
    mapElimView : ∃ (Term α) (ReducesTo _ _)
                → ∃[ (t , els) ∈ Term α × Elims α ] ReducesTo _ _ (applyElims t els)
    mapElimView = λ where (v ⟨ p ⟩) → (elimView v) ⟨ subst0 (λ t → ReducesTo _ s t) (sym $ applyElimView v) p ⟩
  (TDef d dp , els) ⟨ rp ⟩  ← mapElimView <$> reduceTo r sig s fuel
    where
      _ → tcError "can't convert two constructors when their type isn't a definition"
  ifDec (decIn p q)
    (λ where {{refl}} → do
      (DatatypeDef df) ← return $ getDefinition sig d dp
        where
          _ → tcError "can't convert two constructors when their type isn't a datatype"
      con ← liftMaybe (getConstructor f p df)
        "can't find a constructor with such a name"
      params ← liftMaybe (traverse maybeArg els)
        "not all arguments to the datatype are terms"
      psubst ← liftMaybe (listSubst (rezzTel (dataParameterTel df)) params)
        "couldn't construct a substitution for parameters"
      let ctel = substTelescope psubst (conTelescope con)
      csp ← convertSubsts fl ctx ctel lp lq
      return $ CCon p csp)
    (tcError "constructors not convertible")

convLams : Fuel
         → ∀ Γ
           (s : Term α)
           (@0 x y : name)
           (u : Term (x ◃ α))
           (v : Term (y ◃ α))
         → TCM (Conv {α = α} Γ (TLam x u) (TLam y v))
convLams None      ctx  ty         x y u v =
  tcError "can't convert two lambdas when the type isn't a Pi"
convLams (More fl) ctx (TPi z a b) x y u v = do
  let r = rezzScope ctx
  CLam <$> convertCheck fl (ctx , z ∶ a) (unType b) (renameTop r u) (renameTop r v)
convLams (More fl) ctx  ty         x y u v = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  (TPi z a b) ⟨ rp ⟩  ← reduceTo r sig ty fuel
    where
      _ → tcError "can't convert two terms when the type doesn't reduce to a Pi"
  CLam <$> convertCheck fl (ctx , z ∶ a) (unType b) (renameTop r u) (renameTop r v)

convAppsI : Fuel
          → ∀ Γ
            (u u' : Term α)
            (w w' : Elim α)
          → TCM (Σ[ ty ∈ Term α ] (Conv {α = α} Γ (TApp u w) (TApp u' w')))
convAppsI None      ctx u u' w w' =
  tcError "not enough fuel to check conversion of Apps"
convAppsI (More fl) ctx u u' w w' = do
  su Σ, cu ← convertInfer fl ctx u u'
  f Σ, cv  ← convertElims fl ctx su u w w'
  return $ (f $ TApp u) Σ, CApp cu cv

convPis : Fuel
        → ∀ Γ
          (s : Term α)
          (@0 x y : name)
          (u u' : Type α)
          (v  : Type (x ◃ α))
          (v' : Type (y ◃ α))
        → TCM (Conv {α = α} Γ (TPi x u v) (TPi y u' v'))
convPis None      ctx t         x y u u' v v' =
  tcError "not enough fuel to check conversion of Pis"
convPis (More fl) ctx (TSort s) x y u u' v v' = do
  let r = rezzScope ctx

  CPi <$> convertCheck fl ctx (TSort $ typeSort u) (unType u) (unType u')
      <*> convertCheck fl (ctx , x ∶ u) (TSort $ typeSort v) (unType v) (renameTop r (unType v'))
convPis (More fl) ctx  t        x y u u' v v' = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  (TSort s) ⟨ rp ⟩  ← reduceTo r sig t fuel
    where
      _ → tcError "can't convert two terms when the type does not reduce to a sort"
  cu ← convertCheck fl ctx (TSort $ typeSort u) (unType u) (unType u')
  cv ← convertCheck fl (ctx , x ∶ u) (TSort $ typeSort v) (unType v) (renameTop r (unType v'))
  return $ CPi cu cv

convertElims fl ctx (TPi x a b) u (EArg w) (EArg w') = do
  let r = rezzScope ctx
      ksort = piSort (typeSort a) (typeSort b)
  cw ← convertCheck fl ctx (unType a) w w'
  return $ (λ _ → substTop r w (unType b)) Σ, CEArg cw
convertElims fl ctx t           u (EArg w) (EArg w') = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  (TPi x a b) ⟨ rp ⟩  ← reduceTo r sig t fuel
    where
      _ → tcError "can't convert two terms when the type does not reduce to a Pi type"
  let ksort = piSort (typeSort a) (typeSort b)
  cw ← convertCheck fl ctx (unType a) w w'
  return $ (λ _ → substTop r w (unType b)) Σ, CEArg cw
convertElims fl ctx s u w w' = tcError "not implemented yet"

convertSubsts fl ctx tel SNil p = return CSNil
convertSubsts fl ctx tel (SCons x st) p = 
  caseSubstBind p λ where
    y pt {{refl}} → caseTelBind tel λ a rest → do
      let r = rezzScope ctx
      hc ← convertCheck fl ctx (unType a) x y
      tc ← convertSubsts fl ctx (substTelescope (SCons x (idSubst r)) rest) st pt
      return (CSCons hc tc)
    
convertCheck fl ctx ty t q = do
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
      CRedL rpg <$> CRedR rpc <$> convCons fl ctx ty c d p q lc ld
    --for lambda
    (TLam x u ⟨ rpg ⟩ , TLam y v ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convLams fl ctx ty x y u v
    --for app
    (TApp u e ⟨ rpg ⟩ , TApp v f ⟨ rpc ⟩) → do
      snd <$> map2 (λ _ → CRedL rpg ∘ CRedR rpc) <$> convAppsI fl ctx u v e f
    --for pi
    (TPi x tu tv ⟨ rpg ⟩ , TPi y tw tz ⟨ rpc ⟩) → 
      CRedL rpg <$> CRedR rpc <$> convPis fl ctx ty x y tu tw tv tz
    --for sort
    (TSort s ⟨ rpg ⟩ , TSort t ⟨ rpc ⟩) →
      CRedL rpg <$> CRedR rpc <$> convSorts ctx ty s t
    _ → tcError "sorry"

convertInfer fl ctx t q = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  rgty ← reduceTo r sig t fuel
  rcty ← reduceTo r sig q fuel
  case (rgty , rcty) of λ where
    --for vars
    (TVar x p ⟨ rpg  ⟩ , TVar y q ⟨ rpc ⟩) →
      map2 (λ _ → CRedL rpg ∘ CRedR rpc) <$> convVarsI ctx x y p q
    --for defs
    (TDef x p ⟨ rpg  ⟩ , TDef y q  ⟨ rpc ⟩) →
      map2 (λ _ → CRedL rpg ∘ CRedR rpc) <$> convDefsI ctx x y p q
    --for cons
    (TCon c p lc ⟨ rpg  ⟩ , TCon d q ld ⟨ rpc ⟩) →
      tcError "not implemented yet"
    --for lambda
    (TLam x u ⟨ rpg ⟩ , TLam y v ⟨ rpc ⟩) →
      tcError "non inferrable"
    --for app
    (TApp u e ⟨ rpg ⟩ , TApp v f ⟨ rpc ⟩) →
      map2 (λ _ → CRedL rpg ∘ CRedR rpc) <$> convAppsI fl ctx u v e f
    --for pi
    (TPi x tu tv ⟨ rpg ⟩ , TPi y tw tz ⟨ rpc ⟩) →
      tcError "not implemented yet"
    --for sort
    (TSort s ⟨ rpg ⟩ , TSort t ⟨ rpc ⟩) →
      map2 (λ _ → CRedL rpg ∘ CRedR rpc) <$> convSortsI ctx s t
    _ → tcError "sorry"


convert : ∀ Γ (ty : Term α) (t q : Term α) → TCM (Γ ⊢ t ≅ q)
convert ctx ty t q = do
  fl ← tcmFuel
  convertCheck fl ctx ty t q
