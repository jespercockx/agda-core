open import Haskell.Prelude hiding (All; a; b; c; d; s; t)

open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Haskell.Law.Equality renaming (subst to transport)

open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduction.Reduce

module Agda.Core.TypeChecker.Rules.Conversion
  {{@0 globals : Globals}}
  {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x y z          : Name
  @0 α β γ          : Scope Name
  @0 rβ             : RScope Name
  @0 s s' t t' u u' v v' w w' : Term α
  @0 k l n sa sb    : Sort α
  @0 a a' b b' c c' : Type α
  @0 us vs          : TermS α rβ


data Conv      {@0 α} : @0 Term α → @0 Term α → Set
data ConvTermS {@0 α} : @0 TermS α rβ → @0 TermS α rβ → Set

data ConvBranch   {@0 α} {@0 d : NameData} {@0 c : NameCon d} : @0 Branch α c → @0 Branch α c → Set
data ConvBranches {@0 α} {@0 d : NameData} : {@0 cs : RScope(NameCon d)} → @0 Branches α d cs → @0 Branches α d cs → Set where
  CBranchesNil : {bs bp : Branches α d mempty} → ConvBranches bs bp
  CBranchesCons : {@0 cn : NameCon d} {b1 b2 : Branch α cn} {@0 cs : RScope(NameCon d)} {bs1 bs2 : Branches α d cs}
                → ConvBranch b1 b2
                → ConvBranches bs1 bs2
                → ConvBranches (BsCons b1 bs1) (BsCons b2 bs2)

infix 3 Conv
syntax Conv x y        = x ≅ y
syntax ConvTermS us vs = us ⇔ vs

renameTop : Rezz α → Term  (α ▸ x) → Term  (α ▸ y)
renameTop = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTop #-}

renameTopSort : Rezz α → Sort  (α ▸ x) → Sort  (α ▸ y)
renameTopSort = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopSort #-}

renameTopType : Rezz α → Type  (α ▸ x) → Type  (α ▸ y)
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
  CCase  : ∀ {@0 x y z} {u u' : Term α} {@0 r : Rezz α}
           (d : NameData)
           (r1 r2 : Rezz (dataIxScope d))
           (bs bp : Branches α d (AllNameCon d))
           (ms : Type _) (mp : Type _)
         → u ≅ u'
         →   renameTop {y = z} (rezzExtScope r r1) (unType ms)
           ≅ renameTop {y = z} (rezzExtScope r r2) (unType mp)
         → ConvBranches bs bp
         → TCase {x = x} d r1 u bs ms ≅ TCase {x = y} d r2 u' bp mp
  -- TODO: CProj : {!   !}
  CData  : (@0 d : NameData)
           {@0 ps qs : TermS α (dataParScope d)}
           {@0 is ks : TermS α (dataIxScope d)}
         → ps ⇔ qs
         → is ⇔ ks
         → TData d ps is ≅ TData d qs ks
  CCon   : {@0 d : NameData} (c : NameCon d)
           {@0 us vs : TermS α (fieldScope c)}
         → us ⇔ vs
         → TCon c us ≅ TCon c vs
  CRedL  : @0 ReducesTo u u'
         → u' ≅ v
         → u  ≅ v
  CRedR  : @0 ReducesTo v v'
         → u  ≅ v'
         → u  ≅ v

data ConvBranch {α = α} {c = c} where
  CBBranch :  (cr1 cr2 : Rezz c) (r1 r2 : Rezz (fieldScope c))
             (t1 : Term (α ◂▸ fieldScope c)) (t2 : Term (α ◂▸ fieldScope c))
           → t1 ≅ t2
           → ConvBranch (BBranch cr1 r1 t1) (BBranch cr2 r2 t2)


data ConvTermS {α = α} where
  CSNil : ConvTermS {rβ = mempty} us vs
  CSCons : {@0 x : Name}
         → u ≅ v
         → us ⇔ vs
         → (TSCons {x = x} u us) ⇔ (TSCons {x = x} v vs)

-- These have to be here, see https://github.com/agda/agda2hs/issues/346
{-# COMPILE AGDA2HS Conv     #-}
{-# COMPILE AGDA2HS ConvBranch #-}
{-# COMPILE AGDA2HS ConvBranches #-}
{-# COMPILE AGDA2HS ConvTermS #-}
