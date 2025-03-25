open import Haskell.Prelude hiding (All; a; b; c; s; t)

open import Scope

open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Utils.Either
open import Utils.Tactics using (auto)

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Signature
open import Agda.Core.Syntax
open import Agda.Core.Substitute
open import Agda.Core.Reduce

module Agda.Core.Conversion
  {{@0 globals : Globals}}
  {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x y z cn       : Name
  @0 α β γ cs       : Scope Name
  @0 rβ : RScope Name
  @0 s s' t t' u u' v v' w w' : Term α
  @0 k l n sa sb    : Sort α
  @0 a a' b b' c c' : Type α
  @0 us vs          : TermS α rβ

data Conv       {@0 α} : @0 Term α → @0 Term α → Set
data ConvBranch {@0 α} : @0 Branch α cn → @0 Branch α cn → Set
data ConvTermS  {@0 α} : @0 TermS α rβ → @0 TermS α rβ → Set

data ConvBranches {@0 α} : @0 Branches α cs → @0 Branches α cs → Set where
  CBranchesNil : {bs bp : Branches α mempty} → ConvBranches bs bp
  CBranchesCons : {b1 b2 : Branch α cn} {bs1 bs2 : Branches α cs}
                → ConvBranch b1 b2
                → ConvBranches bs1 bs2
                → ConvBranches (BsCons b1 bs1) (BsCons b2 bs2)

infix 3 Conv
syntax Conv x y        = x ≅ y
syntax ConvTermS us vs = us ⇔ vs

renameTop : Rezz α → Term (x ◃ α) → Term (y ◃ α)
renameTop = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTop #-}

renameTopSort : Rezz α → Sort (x ◃ α) → Sort (y ◃ α)
renameTopSort = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopSort #-}

renameTopType : Rezz α → Type (x ◃ α) → Type (y ◃ α)
renameTopType = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopType #-}

data Conv {α} where
  CRefl  : u ≅ u
  CLam   : {@0 r : Rezz α}
         → renameTop {y = z} r u ≅ renameTop {y = z} r v
         → TLam y u ≅ TLam z v
  CPi    : {@0 r : Rezz α}
         → unType a ≅ unType a'
         → unType b ≅ renameTop r (unType b')
         → TPi x a b ≅ TPi y a' b'
  CApp   : u ≅ u'
         → w ≅ w'
         → TApp u w ≅ TApp u' w'
  CCase  : ∀ {@0 x y z cs} {u u' : Term α} {@0 r : Rezz α}
           (d : NameIn dataScope)
           (r1 r2 : Rezz (dataIxScope d))
           (bs bp : Branches α cs)
           (ms : Type _) (mp : Type _)
         → u ≅ u'
         →   renameTop {y = z} (rezzExtScope r r1) (unType ms)
           ≅ renameTop {y = z} (rezzExtScope r r2) (unType mp)
         → ConvBranches bs bp
         → TCase {x = x} d r1 u bs ms ≅ TCase {x = y} d r2 u' bp mp
  -- TODO: CProj : {!   !}
  CData  : (@0 d : NameIn dataScope)
           {@0 ps qs : TermS α (dataParScope d)}
           {@0 is ks : TermS α (dataIxScope d)}
         → ps ⇔ qs
         → is ⇔ ks
         → TData d ps is ≅ TData d qs ks
  CCon   : (c : NameIn conScope)
           {@0 us vs : TermS α (fieldScope c)}
         → us ⇔ vs
         → TCon c us ≅ TCon c vs
  CRedL  : @0 ReducesTo u u'
         → u' ≅ v
         → u  ≅ v
  CRedR  : @0 ReducesTo v v'
         → u  ≅ v'
         → u  ≅ v

data ConvBranch {α} where
  CBBranch : (c : NameIn conScope) (r1 r2 : _)
             (t1 t2 : Term (extScope α (fieldScope c)))
           → t1 ≅ t2
           → ConvBranch (BBranch c r1 t1) (BBranch c r2 t2)


data ConvTermS {α} where
  CSNil : ConvTermS {rβ = Nil} us vs
  CSCons : {@0 x : Name}
         → u ≅ v
         → us ⇔ vs
         → (TSCons {x = x} u us) ⇔ (TSCons {x = x} v vs)

-- These have to be here, see https://github.com/agda/agda2hs/issues/346
{-# COMPILE AGDA2HS Conv     #-}
{-# COMPILE AGDA2HS ConvBranch #-}
{-# COMPILE AGDA2HS ConvBranches #-}
{-# COMPILE AGDA2HS ConvTermS #-}
