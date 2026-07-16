open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce

module Agda.Core.Rules.Conversion
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

opaque
  unfolding RScope

  lengthOfRScope : {@0 rscope : RScope Name} → Singleton rscope → Nat
  lengthOfRScope ([] ⟨ refl ⟩) = zero 
  lengthOfRScope ((Erased name ∷ names) ⟨ refl ⟩) = 
    suc (lengthOfRScope (names ⟨ refl ⟩))

  etaProjTermS : {@0 rscope : RScope Name} → Singleton rscope 
    → (NameInR rscope → Term α) → TermS α rscope
  etaProjTermS ([] ⟨ refl ⟩)                   _  = TSNil
  etaProjTermS ((Erased name ∷ names) ⟨ refl ⟩) f =
    name ↦ f (⟨ name ⟩ inRHere) ◂ etaProjTermS 
      (names ⟨ refl ⟩) 
      (λ where (⟨ x ⟩ p) → f (⟨ x ⟩ inRThere p))
  {-# COMPILE AGDA2HS etaProjTermS #-}


data Conv      {@0 α} : @0 Term α → @0 Term α → Set
data ConvTermS {@0 α} : @0 TermS α rβ → @0 TermS α rβ → Set

data ConvBranch   {@0 α} {@0 d : NameData} {@0 c : NameDataCon d} : @0 Branch α c → @0 Branch α c → Set
data ConvBranches {@0 α} {@0 d : NameData} : {@0 cs : RScope(NameDataCon d)} → @0 Branches α d cs → @0 Branches α d cs → Set where
  CBranchesNil : {bs bp : Branches α d mempty} → ConvBranches bs bp
  CBranchesCons : {@0 cn : NameDataCon d} {b1 b2 : Branch α cn} {@0 cs : RScope(NameDataCon d)} {bs1 bs2 : Branches α d cs}
                → ConvBranch b1 b2
                → ConvBranches bs1 bs2
                → ConvBranches (BsCons b1 bs1) (BsCons b2 bs2)

infix 3 Conv
syntax Conv x y        = x ≅ y
syntax ConvTermS us vs = us ⇔ vs

renameTop : Singleton α → Term  (α ▸ x) → Term  (α ▸ y)
renameTop = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTop #-}

renameTopSort : Singleton α → Sort  (α ▸ x) → Sort  (α ▸ y)
renameTopSort = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopSort #-}

renameTopType : Singleton α → Type  (α ▸ x) → Type  (α ▸ y)
renameTopType = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopType #-}


data Conv {α} where
  CRefl  : u ≅ u
  CLam   : {@0 r : Singleton α}
         → renameTop {y = z} r u ≅ renameTop {y = z} r v
         → TLam y u ≅ TLam z v
  CPi    : {@0 r : Singleton α}
         → unType a ≅ unType a'
         → unType b ≅ renameTop r (unType b')
         → TPi x a b ≅ TPi y a' b'
  CApp   : u ≅ u'
         → w ≅ w'
         → TApp u w ≅ TApp u' w'
  CCase  : ∀ {@0 x y z} {u u' : Term α} {@0 r : Singleton α}
           (d : NameData)
           (r1 r2 : Singleton (dataIxScope d))
           (bs bp : Branches α d (AllNameCon d))
           (ms : Type _) (mp : Type _)
         → u ≅ u'
         →   renameTop {y = z} (singExtScope r r1) (unType ms)
           ≅ renameTop {y = z} (singExtScope r r2) (unType mp)
         → ConvBranches bs bp
         → TCase {x = x} d r1 u bs ms ≅ TCase {x = y} d r2 u' bp mp
  CProj : 
          {rn : NameRec}
          {f : NameProj rn}
          {recTerm1 recTerm2 : Term α}
          → recTerm1 ≅ recTerm2
          → (TProj recTerm1 f) ≅ (TProj recTerm2 f)
  CData  : (@0 d : NameData)
           {@0 ps qs : TermS α (dataParScope d)}
           {@0 is ks : TermS α (dataIxScope d)}
         → ps ⇔ qs
         → is ⇔ ks
         → TData d ps is ≅ TData d qs ks
  CRec : (@0 rn : NameRec)
         (@0 pars1 pars2 : TermS α (recParScope rn))
         → pars1 ⇔ pars2
         → TRec rn pars1 ≅ TRec rn pars2 
  CDataCon : {@0 d : NameData} (c : NameDataCon d)
           {@0 us vs : TermS α (dataFieldScope c)}
         → us ⇔ vs
         → TDataCon c us ≅ TDataCon c vs
  CRecCon : (rn : NameRec) 
            {@0 args1 args2 : TermS α (recFieldScope rn)}
          → args1 ⇔ args2
          → TRecCon rn args1 ≅ TRecCon rn args2
  CEtaFunctionsLeft : (@0 x : Name) (f : Term α) (b : Term (α ▸ x)) → 
    let subsetProof = subWeaken subRefl in
      b ≅ (TApp (weakenTerm subsetProof f) (TVar (VZero x)))
      → f ≅ (TLam x b)
  CEtaFunctionsRight : (@0 x : Name) (f : Term α) (b : Term (α ▸ x)) → 
    let subsetProof = subWeaken subRefl in
      b ≅ (TApp (weakenTerm subsetProof f) (TVar (VZero x)))
      → (TLam x b) ≅ f 
  CEtaRecordsLeft : 
    (rn : NameRec) 
    (rt : Term α) 
    (argsTermS : TermS α (recFieldScope rn))
    (singScope : Singleton (recFieldScope rn))
    -- (proofNonEmpty : ∃ Nat (λ n → lengthOfRScope singScope ≡ suc n))
    → let func = (TProj {rn = rn} rt)
          termSToConvertInto = etaProjTermS singScope func
          in
      (argsTermS ⇔ termSToConvertInto)
    → rt ≅ (TRecCon rn argsTermS)
  CEtaRecordsRight : 
    (rn : NameRec) 
    (rt : Term α)
    (argsTermS : TermS α (recFieldScope rn))
    (singScope : Singleton (recFieldScope rn))
    -- (proofNonEmpty : ∃ Nat (λ n → lengthOfRScope singScope ≡ suc n))
    → let func = (TProj {rn = rn} rt)
          termSToConvertInto = etaProjTermS singScope func
          in
      (argsTermS ⇔ termSToConvertInto)
    → (TRecCon rn argsTermS) ≅ rt 
  CRedL  : @0 ReducesTo u u'
         → u' ≅ v
         → u  ≅ v
  CRedR  : @0 ReducesTo v v'
         → u  ≅ v'
         → u  ≅ v
  
  

data ConvBranch {α = α} {c = c} where
  CBBranch :  (cr1 cr2 : Singleton c) (r1 r2 : Singleton (dataFieldScope c))
             (t1 : Term (α ◂▸ dataFieldScope c)) (t2 : Term (α ◂▸ dataFieldScope c))
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
