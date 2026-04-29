open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce

module Agda.Core.Rules.TypedConversion
  {{@0 globals : Globals}}
  {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals


private variable
  @0 x y z          : Name
  @0 α β γ          : Scope Name
  @0 s s' t t' u u' v v' w w' : Term α

-- opaque
--   unfolding RScope
--   etaProjTermS : {@0 rscope : RScope Name} → Singleton rscope → (NameInR rscope → Term α) → TermS α rscope
--   etaProjTermS ([] ⟨ refl ⟩)                   _  = TSNil
--   etaProjTermS ((Erased name ∷ names) ⟨ refl ⟩) f =
--     name ↦ f (⟨ name ⟩ inRHere) ◂ etaProjTermS (names ⟨ refl ⟩) (λ where (⟨ x ⟩ p) → f (⟨ x ⟩ inRThere p))
--   {-# COMPILE AGDA2HS etaProjTermS #-}


data Conv      {@0 α} (@0 Γ : Context α) : @0 Term α → @0 Term α → Set
data ConvTermS {@0 α} (@0 Γ : Context α) : (@0 rβ : RScope Name) → @0 TermS α rβ → @0 TermS α rβ → Set


infix 3 Conv
syntax Conv Γ x y        = Γ ⊢ x ≅ y
syntax ConvTermS Γ rscope us vs = Γ [ rscope ]  ⊢ us ⇔ vs 

renameTop : Singleton α → Term  (α ▸ x) → Term  (α ▸ y)
renameTop = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTop #-}

renameTopSort : Singleton α → Sort  (α ▸ x) → Sort  (α ▸ y)
renameTopSort = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopSort #-}

renameTopType : Singleton α → Type  (α ▸ x) → Type  (α ▸ y)
renameTopType = subst ∘ liftBindSubst ∘ idSubst

{-# COMPILE AGDA2HS renameTopType #-}


data Conv {α} Γ where
  CRefl : Γ ⊢ u ≅ u





data ConvTermS {α} Γ where
  CSNil : (us vs : TermS α mempty) → ConvTermS Γ mempty us vs
  CSCons : {@0 x : Name} {@0 rscope : RScope Name}
          (us vs : TermS α rscope)
          → Γ ⊢ u ≅ v
          → Γ [ rscope ] ⊢ us ⇔ vs
           → Γ [ rbind x rscope ] ⊢ (TSCons {x = x} u us) ⇔ (TSCons {x = x} v vs)



-- These have to be here, see https://github.com/agda/agda2hs/issues/346
{-# COMPILE AGDA2HS Conv     #-}
-- {-# COMPILE AGDA2HS ConvBranch #-}
-- {-# COMPILE AGDA2HS ConvBranches #-}
{-# COMPILE AGDA2HS ConvTermS #-}
