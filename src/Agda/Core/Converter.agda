open import Haskell.Prelude renaming (_,_ to _,p_; _×_ to _×p_)
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
open import Agda.Core.Utils --renaming (_,_ to _Σ,_)

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



convVars : (Γ : Context α)
           (s : Term α)
           (@0 x y : name)
           (p : x ∈ α) (q : y ∈ α)
         → TCM (Conv (TVar x p) (TVar y q))
convVars ctx _ x y p q =
  ifDec (decIn p q)
    (λ where {{refl}} → return CRefl)
    (tcError "variables not convertible")

convVarsI : (Γ : Context α)
            (@0 x y : name)
            (p : x ∈ α) (q : y ∈ α)
          → TCM (Σ[ ty ∈ Term α ] ((TVar x p) ≅ (TVar y q)))
convVarsI ctx x y p q =
  ifDec (decIn p q)
    (λ where {{refl}} → return $ (unType $ lookupVar ctx x p) , CRefl)
    (tcError "variables not convertible")

convDefs : (Γ : Context α)
           (s : Term α)
           (@0 f g : name)
           (p : f ∈ defScope)
           (q : g ∈ defScope)
         → TCM (Conv {α = α} (TDef f p) (TDef g q))
convDefs ctx s f g p q =
  ifDec (decIn p q)
    (λ where {{refl}} → return CRefl)
    (tcError "definitions not convertible")

convDefsI : (Γ : Context α)
            (@0 f g : name)
            (p : f ∈ defScope)
            (q : g ∈ defScope)
          → TCM (Σ[ ty ∈ Term α ] (Conv {α = α} (TDef f p) (TDef g q)))
convDefsI ctx f g p q = do
  rezz sig ← tcmSignature
  let ty = unType $ weakenType subEmpty $ getType sig f p
  ifDec (decIn p q)
    (λ where {{refl}} → return $ ty , CRefl)
    (tcError "definitions not convertible")

convSorts : (Γ : Context α)
            (s : Term α)
            (u u' : Sort α)
          → TCM (Conv {α = α} (TSort u) (TSort u'))
convSorts ctx s (STyp u) (STyp u') =
  ifDec ((u == u') ⟨ isEquality u u' ⟩)
    (λ where {{refl}} → return $ CRefl)
    (tcError "can't convert two different sorts")

convSortsI : (Γ : Context α)
             (u u' : Sort α)
           → TCM (Σ[ ty ∈ Term α ] (Conv {α = α} (TSort u) (TSort u')))
convSortsI ctx (STyp u) (STyp u') =
  ifDec ((u == u') ⟨ isEquality u u' ⟩)
    (λ where {{refl}} → return $ (TSort $ sucSort $ STyp u) , CRefl)
    (tcError "can't convert two different sorts")

convertCheck : Fuel → (Γ : Context α) (ty : Term α) (t q : Term α) → TCM (t ≅ q)
convertInfer : Fuel → (Γ : Context α) (t q : Term α) → TCM (Σ (Term α) (λ ty → t ≅ q))
convertElims : Fuel →
               (Γ : Context α)
               (tu   : Term α)
               (u    : Term α)
               (v v' : Elim α)
             → TCM (Σ (Term α) (λ _ → v ≃ v'))
convertSubsts : Fuel →
              ∀ {@0 α β} (Γ : Context α)
                (ty : Telescope α β)
                (s p : β ⇒ α)
              → TCM (s ⇔ p)
convertBranches : Fuel →
                ∀ {@0 x : name} {@0 cons : Scope name} (Γ : Context α)
                  (dt : Datatype)
                  (ps : dataPars dt ⇒ α)
                  (rty : Term (x ◃ α))
                  (bs bp : Branches α cons)
                → TCM (ConvBranches bs bp)

convCons : Fuel →
           (Γ : Context α)
           (s : Term α)
           (@0 f g : name)
           (p : f ∈ conScope)
           (q : g ∈ conScope)
           (lp : fieldsOf p ⇒ α)
           (lq : fieldsOf q ⇒ α)
         → TCM (Conv {α = α} (TCon f p lp) (TCon g q lq))
convCons         None      ctx s f g p q lp lq =
  tcError "not enough fuel to convert two constructors"
convCons {α = α} (More fl) ctx s f g p q lp lq = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature
  (TDef d dp ,p els) ⟨ rp ⟩  ← reduceElimView sig s <$> reduceTo r sig s fuel
    where
      _ → tcError "can't convert two constructors when their type isn't a definition"
  ifDec (decIn p q)
    (λ where {{refl}} → do
      (DatatypeDef df) ← return $ getDefinition sig d dp
        where
          _ → tcError "can't convert two constructors when their type isn't a datatype"
      cdi ⟨ refl ⟩ ← liftMaybe (getConstructor f p df)
        "can't find a constructor with such a name"
      let (_ , con) = lookupAll (dataConstructors df) cdi
      params ← liftMaybe (traverse maybeArg els)
        "not all arguments to the datatype are terms"
      (psubst ,p _) ← liftMaybe (listSubst (rezzTel (dataParTel df)) params)
        "couldn't construct a substitution for parameters"
      let ctel = substTelescope psubst (conTelescope con)
      csp ← convertSubsts fl ctx ctel lp lq
      return $ CCon p csp)
    (tcError "constructors not convertible")

convLams : Fuel
         → (Γ : Context α)
           (s : Term α)
           (@0 x y : name)
           (u : Term (x ◃ α))
           (v : Term (y ◃ α))
         → TCM (Conv {α = α} (TLam x u) (TLam y v))
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
          → (Γ : Context α)
            (u u' : Term α)
            (w w' : Elim α)
          → TCM (Σ[ ty ∈ Term α ] (Conv {α = α} (TApp u w) (TApp u' w')))
convAppsI None      ctx u u' w w' =
  tcError "not enough fuel to check conversion of Apps"
convAppsI (More fl) ctx u u' w w' = do
  su , cu ← convertInfer fl ctx u u'
  sw , cv  ← convertElims fl ctx su u w w'
  return $ sw , CApp cu cv

convPisI : Fuel →
           (Γ : Context α)
           (@0 x y : name)
           (u u' : Type α)
           (v  : Type (x ◃ α))
           (v' : Type (y ◃ α))
         → TCM (Σ[ ty ∈ Term α ] (Conv {α = α} (TPi x u v) (TPi y u' v')))
convPisI fl ctx x y u u' v v' = do
  let r  = rezzScope ctx
      ps = TSort (piSort (typeSort u) (typeSort v))
  cpi ← CPi <$> convertCheck fl ctx (TSort $ typeSort u) (unType u) (unType u')
            <*> convertCheck fl (ctx , x ∶ u) (TSort $ typeSort v) (unType v) (renameTop r (unType v'))
  return (ps , cpi)

convPis : Fuel →
           (Γ : Context α)
           (s : Term α)
           (@0 x y : name)
           (u u' : Type α)
           (v  : Type (x ◃ α))
           (v' : Type (y ◃ α))
         → TCM (Conv {α = α} (TPi x u v) (TPi y u' v'))
convPis None      _   _ _ _ _ _  _ _  = tcError "not enough fuel"
convPis (More fl) ctx _ x y u u' v v' = snd <$> convPisI fl ctx x y u u' v v'

convertElims fl ctx (TPi x a b) u (EArg w) (EArg w') = do
  let r = rezzScope ctx
      ksort = piSort (typeSort a) (typeSort b)
  cw ← convertCheck fl ctx (unType a) w w'
  return $ substTop r w (unType b) , CEArg cw
convertElims fl ctx t           u (EArg w) (EArg w') = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  (TPi x a b) ⟨ rp ⟩  ← reduceTo r sig t fuel
    where
      _ → tcError "can't convert two terms when the type does not reduce to a Pi type"
  let ksort = piSort (typeSort a) (typeSort b)
  cw ← convertCheck fl ctx (unType a) w w'
  return $ substTop r w (unType b) , CEArg cw
convertElims fl ctx tu u (ECase ws m) (ECase ws' m') = do
  let r = rezzScope ctx
  rezz sig  ← tcmSignature
  (TDef d dp ,p els) ⟨ rp ⟩  ← reduceElimView _ _ <$> reduceTo r sig tu fl
    where
      _ → tcError "can't typecheck a constrctor with a type that isn't a def application"
  (DatatypeDef df) ⟨ dep ⟩ ← return $ witheq (getDefinition sig d dp)
    where
      _ → tcError "can't convert two constructors when their type isn't a datatype"
  params ← liftMaybe (traverse maybeArg els)
    "not all arguments to the datatype are terms"
  (psubst ,p _) ← liftMaybe (listSubst (rezzTel (dataParTel df)) params)
    "couldn't construct a substitution for parameters"
  (Erased refl) ← liftMaybe
    (allInScope {γ = conScope} (allBranches ws) (allBranches ws'))
    "couldn't verify that branches cover the same constructors"
  cm ← convertCheck fl (ctx , _ ∶ El (substSort psubst $ dataSort df) tu)
                       (TSort (typeSort m))
                       (renameTop r (unType m))
                       (renameTop r (unType m'))
  cbs ← convertBranches fl ctx df psubst (unType m) ws ws'
  return (substTop r u (unType m) , CECase ws ws' m m' cm cbs)
convertElims fl ctx s u _           _ = tcError "two elims aren't the same shape"

convertSubsts fl ctx tel SNil p = return CSNil
convertSubsts fl ctx tel (SCons x st) p =
  caseSubstBind p λ where
    y pt {{refl}} → caseTelBind tel λ a rest → do
      let r = rezzScope ctx
      hc ← convertCheck fl ctx (unType a) x y
      tc ← convertSubsts fl ctx (substTelescope (SCons x (idSubst r)) rest) st pt
      return (CSCons hc tc)

convertBranch : Fuel
              → ∀ {@0 x con : name} (Γ : Context α)
                  (dt : Datatype)
                  (ps : dataPars dt ⇒ α)
                  (rt : Term (x ◃ α))
              → (b1 b2 : Branch α con)
              → TCM (ConvBranch b1 b2)
convertBranch fl ctx dt ps rt (BBranch _ cp1 rz1 rhs1) (BBranch _ cp2 rz2 rhs2) =
  ifDec (decIn cp1 cp2)
    (λ where {{refl}} → do
      let r = rezzScope ctx
      cid ⟨ refl ⟩  ← liftMaybe (getConstructor _ cp1 dt)
         "can't find a constructor with such a name"
      let (_ , con) = lookupAll (dataConstructors dt) cid
          ctel = substTelescope ps (conTelescope con)
          cargs = weakenSubst (subJoinHere (rezzCong revScope rz1) subRefl)
                              (revIdSubst rz1)
          idsubst = weakenSubst (subJoinDrop (rezzCong revScope rz1) subRefl)
                                (idSubst r)
          bsubst = SCons (TCon _ cp1 cargs) idsubst
      CBBranch _ cp1 rz1 rz2 rhs1 rhs2 <$>
        convertCheck fl (addContextTel ctel ctx) (substTerm bsubst rt) rhs1 rhs2)
    (tcError "can't convert two branches that match on different constructors")

convertBranches fl ctx df pars rt BsNil        bp = return CBranchesNil
convertBranches fl ctx df pars rt (BsCons bsh bst) bp =
  caseBsCons bp (λ where
    bph bpt {{refl}} → CBranchesCons <$> convertBranch fl ctx df pars rt bsh bph <*> convertBranches fl ctx df pars rt bst bpt)


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
    --let and ann shoudln't appear here since they get reduced away
    _ → tcError "two terms are not the same and aren't convertible"

convertInfer fl ctx t q = do
  let r = rezzScope ctx
  fuel      ← tcmFuel
  rezz sig  ← tcmSignature

  rt ← reduceTo r sig t fuel
  rq ← reduceTo r sig q fuel
  case (rt , rq) of λ where
    --for vars
    (TVar x p ⟨ rpt  ⟩ , TVar y q ⟨ rpq ⟩) →
      map2 (λ _ → CRedL rpt ∘ CRedR rpq) <$> convVarsI ctx x y p q
    --for defs
    (TDef x p ⟨ rpt  ⟩ , TDef y q  ⟨ rpq ⟩) →
       map2 (λ _ → CRedL rpt ∘ CRedR rpq) <$> convDefsI ctx x y p q
    --for cons
    (TCon c p lc ⟨ rpt  ⟩ , TCon d q ld ⟨ rpq ⟩) →
      tcError "non inferrable"
    --for lambda
    (TLam x u ⟨ rpt ⟩ , TLam y v ⟨ rpq ⟩) →
      tcError "non inferrable"
    --for app
    (TApp u e ⟨ rpt ⟩ , TApp v f ⟨ rpq ⟩) →
      map2 (λ _ → CRedL rpt ∘ CRedR rpq) <$> convAppsI fl ctx u v e f
    --for pi
    (TPi x tu tv ⟨ rpt ⟩ , TPi y tw tz ⟨ rpq ⟩) →
      map2 (λ _ → CRedL rpt ∘ CRedR rpq) <$> convPisI fl ctx x y tu tw tv tz
    --for sort
    (TSort s ⟨ rpt ⟩ , TSort t ⟨ rpq ⟩) →
      map2 (λ _ → CRedL rpt ∘ CRedR rpq) <$> convSortsI ctx s t
    --let and ann shoudln't appear here since they get reduced away
    _ → tcError "two terms are not the same and aren't convertible"

convert : (Γ : Context α) (ty : Term α) (t q : Term α) → TCM (t ≅ q)
convert ctx ty t q = do
  fl ← tcmFuel
  convertCheck fl ctx ty t q
