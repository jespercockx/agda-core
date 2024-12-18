open import Haskell.Prelude
open import Haskell.Extra.Erase
open import Haskell.Law.Equality

open import Scope


open import Agda.Core.Name

module Agda.Core.ScopeUtils where

module Shrink where
  private variable
    @0 α β : Scope Name
    x : Name

  data Shrink : (@0 α β : Scope Name) → Set where
    ShNil  : Shrink mempty β
    ShKeep : (@0 x : Name) → Shrink α β → Shrink (x ◃ α) (x ◃ β)
    ShCons : (@0 x : Name) → Shrink α β → Shrink α (x ◃ β)

  opaque
    unfolding Scope
    idShrink : Rezz α → Shrink α α
    idShrink (rezz []) = ShNil
    idShrink (rezz (Erased x ∷ α)) = ShKeep x (idShrink (rezz α))

  ShrinkToSub : Shrink α β →  α ⊆ β
  ShrinkToSub ShNil = subEmpty
  ShrinkToSub (ShKeep x s) = subBindKeep (ShrinkToSub s)
  ShrinkToSub (ShCons x s) = subBindDrop (ShrinkToSub s)

  opaque
    unfolding Sub Split
    SubToShrink : Rezz β → α ⊆ β → Shrink α β
    SubToShrink _ (⟨ γ ⟩ EmptyL) = ShNil
    SubToShrink βRun (⟨ γ ⟩ EmptyR) = idShrink βRun
    SubToShrink βRun (⟨ γ ⟩ ConsL x p) = ShKeep x (SubToShrink (rezzUnbind βRun) < p >)
    SubToShrink βRun (⟨ γ ⟩ ConsR y p) = ShCons y (SubToShrink (rezzUnbind βRun) < p >)
  {-
  opaque
    unfolding Sub Split SubToShrink splitEmptyLeft
    ShrinkEquivLeft : (βRun : Rezz β) (s : Shrink α β) → SubToShrink βRun (ShrinkToSub s) ≡ s
    ShrinkEquivLeft βRun ShNil = refl
    ShrinkEquivLeft βRun (ShKeep x s) = do
      let e = ShrinkEquivLeft (rezzUnbind βRun) s
      subst (λ z → SubToShrink βRun (ShrinkToSub (ShKeep x s)) ≡ ShKeep x z ) e {!   !}
    ShrinkEquivLeft βRun (ShCons x s) = do
      let e = ShrinkEquivLeft (rezzUnbind βRun) s
      subst (λ z → SubToShrink βRun (ShrinkToSub (ShCons x s)) ≡ ShCons x z ) e {!   !}
  -}
{- End of module Shrink -}