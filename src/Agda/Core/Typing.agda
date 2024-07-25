open import Scope
import Utils.List as List

open import Haskell.Prelude hiding (All; a; b; c; e; s; t; m)

open import Haskell.Extra.Erase
open import Haskell.Extra.Loop
open import Haskell.Law.Equality

open import Utils.Tactics using (auto)

open import Agda.Core.GlobalScope using (Globals; Name)
open import Agda.Core.Signature
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.Conversion
open import Agda.Core.Context
open import Agda.Core.Substitute
open import Agda.Core.Utils

module Agda.Core.Typing
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x y con : Name
  @0 α β pars ixs cons : Scope Name
  @0 s t u v : Term α
  @0 a b c   : Type α
  @0 k l m   : Sort α
  @0 n       : Nat
  @0 tel     : Telescope α β
  @0 us vs   : α ⇒ β

constructorType : (@0 d : Name) {@(tactic auto) dp : d ∈ dataScope}
                → (@0 c : Name) {@(tactic auto) cp : c ∈ conScope}
                → (con : Constructor (dataParScope d) (dataIxScope d) c cp)
                → Sort α
                → (pars : dataParScope d ⇒ α)
                → fieldScope c ⇒ α
                → Type α
constructorType d c con ds pars us =
  dataType d ds pars (substSubst (concatSubst (revSubst us) pars) (conIndices con))
{-# COMPILE AGDA2HS constructorType #-}

data TyTerm (@0 Γ : Context α) : @0 Term α → @0 Type α → Set

data TySubst (@0 Γ : Context α) : @0 (β ⇒ α) → @0 Telescope α β → Set

data TyBranches (@0 Γ : Context α)
                {@0 pars ixs} (@0 dt : Datatype pars ixs)
                (@0 ps : pars ⇒ α)
                (@0 rt : Type (x ◃ α)) : @0 Branches α cons → Set

data TyBranch (@0 Γ : Context α)
              {@0 pars ixs} (@0 dt : Datatype pars ixs)
              (@0 ps : pars ⇒ α)
              (@0 rt : Type (x ◃ α)) : @0 Branch α con → Set

infix 3 TyTerm
syntax TyTerm Γ u t = Γ ⊢ u ∶ t

data TyTerm {α} Γ where

  TyTVar
    : (@0 x : Name) {@(tactic auto) p : x ∈ α}
    ----------------------------------
    → Γ ⊢ TVar x ∶ lookupVar Γ x

  TyDef
    : (@0 f : Name) {@(tactic auto) p : f ∈ defScope}
    ----------------------------------------------
    → Γ ⊢ TDef f ∶ weakenType subEmpty (getType sig f)

  TyData
    : (@0 d : Name) {@(tactic auto) dp : d ∈ dataScope}
    → (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d {dp} ≡ dt
    → {@0 pars : dataParScope d ⇒ α}
    → {@0 ixs : dataIxScope d ⇒ α}
    → TySubst Γ pars (weakenTel subEmpty (dataParameterTel dt))
    → TySubst Γ ixs (substTelescope pars (dataIndexTel dt))
    ----------------------------------------------
    → Γ ⊢ dataTypeTerm d pars ixs ∶ sortType (substSort pars (dataSort dt))

  TyCon
    : (@0 d : Name) {@(tactic auto) dp : d ∈ dataScope}
    → (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d {dp} ≡ dt
    → (@0 c : Name) {@(tactic auto) cq : c ∈ dataConstructorScope dt}
    → (let (cp , con) = dataConstructors dt c)
    → {@0 pars : dataParScope d ⇒ α}
    → {@0 us : fieldScope c {cp} ⇒ α}
    → TySubst Γ us (substTelescope pars (conTelescope con))
    -----------------------------------------------------------
    → Γ ⊢ TCon c {cp} us ∶ constructorType d {dp} c {cp} con (substSort pars (dataSort dt)) pars us

  TyLam
    : {@0 r : Rezz α}
    → Γ , x ∶ a ⊢ u ∶ renameTopType r b
    -------------------------------
    → Γ ⊢ TLam x u ∶ El k (TPi y a b)

  TyApp
    : {b : Type α} {@0 r : Rezz α}
    → Γ ⊢ u ∶ a
    → (unType a) ≅ TPi x b c
    → Γ ⊢ v ∶ b
    ------------------------------------
    → Γ ⊢ TApp u v ∶ substTopType r v c

  TyCase
    : {@0 r : Rezz α}
      (@0 d : Name) {@(tactic auto) dp : d ∈ dataScope}
      (@0 dt : Datatype (dataParScope d) (dataIxScope d)) → @0 sigData sig d ≡ dt →
      {@0 ps : dataParScope d ⇒ α}
      {@0 is : dataIxScope d ⇒ α}
      (bs : Branches α (dataConstructorScope dt))
      (rt : Type (x ◃ α))
    → Γ ⊢ u ∶ a
    → (unType a) ≅ (unType $ dataType d k ps is)
    → TyBranches Γ dt ps rt bs
    → Γ ⊢ TCase u bs rt ∶ (substTopType r u rt)

  -- TODO: proj

  TyPi
    : Γ ⊢ u ∶ sortType k
    → Γ , x ∶ (El k u) ⊢ v ∶ sortType l
    ----------------------------------------------------------
    → Γ ⊢ TPi x (El k u) (El l v) ∶ sortType (piSort k l)

  TyType
    -------------------------------------------
    : Γ ⊢ TSort k ∶ sortType (sucSort k)

  TyLet
    : {@0 r : Rezz α}
    → Γ ⊢ u ∶ a
    → Γ , x ∶ a ⊢ v ∶ weakenType (subWeaken subRefl) b
    ----------------------------------------------
    → Γ ⊢ TLet x u v ∶ b

  TyAnn
    : Γ ⊢ u ∶ a
    ------------------
    → Γ ⊢ TAnn u a ∶ a

  TyConv
    : Γ ⊢ u ∶ a
    → (unType a) ≅ (unType b)
    ----------------
    → Γ ⊢ u ∶ b

{-# COMPILE AGDA2HS TyTerm #-}

data TyBranches {α} Γ dt ps rt where
  TyBsNil : TyBranches Γ dt ps rt BsNil
  TyBsCons : ∀ {@0 b : Branch α con} {@0 bs : Branches α cons}
           → TyBranch Γ dt ps rt b
           → TyBranches Γ dt ps rt bs
           → TyBranches Γ dt ps rt (BsCons b bs)

data TyBranch {α} Γ dt ps rt where
  TyBBranch : (@0 c : Name) → (c∈dcons : c ∈ dataConstructorScope dt)
            → (let (c∈cons , con ) = dataConstructors dt c)
            → {@0 r : Rezz (fieldScope c {c∈cons})}
              {@0 rα : Rezz α}
              (rhs : Term (~ fieldScope c {c∈cons} <> α))
              (let ctel = substTelescope ps (conTelescope con)
                   cargs = weakenSubst (subJoinHere (rezzCong revScope r) subRefl)
                                       (revIdSubst r)
                   idsubst = weakenSubst (subJoinDrop (rezzCong revScope r) subRefl)
                                         (idSubst rα)
                   bsubst = SCons (TCon c {c∈cons} cargs) idsubst)
            → TyTerm (addContextTel ctel Γ) rhs (substType bsubst rt)
            → TyBranch Γ dt ps rt (BBranch c {c∈cons} r rhs)

data TySubst {α} Γ where
  TyNil  : TySubst Γ SNil EmptyTel
  TyCons : {@0 r : Rezz α}
         → TyTerm Γ u a
         → TySubst Γ us (substTelescope (SCons u (idSubst r)) tel)
         → TySubst Γ (SCons u us) (ExtendTel x a tel)

{-# COMPILE AGDA2HS TySubst #-}

{-
-- TyElims Γ es f t₁ t₂ means: if  Γ ⊢ h [] : t₁  then  Γ ⊢ h es : t₂
data TyElims Γ where
    TyDone : ∀ {@0 u} → TyElims Γ [] u t t
    TyMore : ∀ {@0 h f}
        → TyElim  Γ e        s             f
        → TyElims Γ es       (h ∘ (e ∷_)) (f h) t
        → TyElims Γ (e ∷ es) h             s    t

{-# COMPILE AGDA2HS TyElims #-}
-}
