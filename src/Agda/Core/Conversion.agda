open import Haskell.Prelude hiding (All; a; b; c; s; t)

open import Scope

open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Utils.Either
open import Utils.Tactics using (auto)

open import Agda.Core.GlobalScope using (Globals; Name)
open import Agda.Core.Signature
open import Agda.Core.Syntax
open import Agda.Core.Substitute
open import Agda.Core.Reduce
open import Agda.Core.Context
open import Agda.Core.Utils

module Agda.Core.Conversion
  {{@0 globals : Globals}}
  {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x y z cn       : Name
  @0 α β γ cs       : Scope Name
  @0 s s' t t' u u' v v' w w' : Term α
  @0 k l n sa sb    : Sort α
  @0 a a' b b' c c' : Type α
  @0 tel            : Telescope α β
  @0 us vs          : α ⇒ β

data Conv       {@0 α} : @0 Term α → @0 Term α → Set
data ConvBranch {@0 α} : @0 Branch α cn → @0 Branch α cn → Set
data ConvSubst  {@0 α} : @0 β ⇒ α → @0 β ⇒ α → Set

data ConvBranches {@0 α} : @0 Branches α cs → @0 Branches α cs → Set where
  CBranchesNil : {bs bp : Branches α mempty} → ConvBranches bs bp
  CBranchesCons : {b1 b2 : Branch α cn} {bs1 bs2 : Branches α cs}
                → ConvBranch b1 b2
                → ConvBranches bs1 bs2
                → ConvBranches (BsCons b1 bs1) (BsCons b2 bs2)


{-# COMPILE AGDA2HS Conv     #-}
{-# COMPILE AGDA2HS ConvBranch #-}
{-# COMPILE AGDA2HS ConvBranches #-}
{-# COMPILE AGDA2HS ConvSubst #-}

infix 3 Conv
syntax Conv x y        = x ≅ y
syntax ConvSubst us vs = us ⇔ vs

renameTop : Rezz α → Term (x ◃ α) → Term (y ◃ α)
renameTop = substTerm ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTop #-}

renameTopSort : Rezz α → Sort (x ◃ α) → Sort (y ◃ α)
renameTopSort = substSort ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopSort #-}

renameTopType : Rezz α → Type (x ◃ α) → Type (y ◃ α)
renameTopType = substType ∘ liftBindSubst ∘ idSubst

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
  CCase  : {@0 r : Rezz α}
           (bs bp : Branches α cs)
           (ms : Type (x ◃ α)) (mp : Type (y ◃ α))
         → u ≅ u'
         → renameTop {y = z} r (unType ms) ≅ renameTop {y = z} r (unType mp)
         → ConvBranches bs bp
         → TCase u bs ms ≅ TCase u' bp mp
  -- TODO: CProj : {!   !}
  CData  : (@0 d : Name) {@(tactic auto) cd : d ∈ dataScope}
           {@0 ps qs : dataParScope d ⇒ α}
           {@0 is ks : dataIxScope d ⇒ α}
         → ps ⇔ qs
         → is ⇔ ks
         → TData d ps is ≅ TData d qs ks
  CCon   : (@0 c : Name) {@(tactic auto) cp : c ∈ conScope}
           {@0 us vs : fieldScope c ⇒ α}
         → us ⇔ vs
         → TCon c us ≅ TCon c vs
  CRedL  : @0 ReducesTo u u'
         → u' ≅ v
         → u  ≅ v
  CRedR  : @0 ReducesTo v v'
         → u  ≅ v'
         → u  ≅ v

data ConvBranch {α} where
  CBBranch : (@0 c : Name) (cp : c ∈ conScope) (r1 r2 : _)
             (t1 t2 : Term (~ fieldScope c <> α))
           → t1 ≅ t2
           → ConvBranch (BBranch c r1 t1) (BBranch c r2 t2)


data ConvSubst {α} where
  CSNil : ConvSubst {β = mempty} us vs
  CSCons : {@0 x : Name}
         → u ≅ v
         → us ⇔ vs
         → (SCons {x = x} u us) ⇔ (SCons {x = x} v vs)
