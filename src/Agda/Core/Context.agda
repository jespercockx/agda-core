open import Scope

open import Utils.Either
open import Utils.Tactics using (auto)
open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Haskell.Law.Equality
open import Haskell.Law.Monoid
open import Haskell.Prelude hiding (All; s; t)

open import Agda.Core.Name
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Syntax

module Agda.Core.Context
  {{@0 globals : Globals}}
  where

private variable
  @0 x y : Name
  @0 α β : Scope Name
  @0 rβ : RScope Name
  @0 s t u v : Term α

data Context : @0 Scope Name → Set where
  CtxEmpty  : Context mempty
  CtxExtend : Context α → (@0 x : Name) → Type α → Context  (α ▸ x)
  CtxExtendLet : Context α → (@0 x : Name) → Term α → Type α → Context  (α ▸ x)
{-# COMPILE AGDA2HS Context #-}

pattern ⌈⌉ = CtxEmpty
pattern _,_∶_ g x ty = CtxExtend g x ty
pattern _,_≔_∶_ g x u ty = CtxExtendLet g x u ty

infixl 4 _,_∶_
infixl 4 _,_≔_∶_

private variable
  @0 Γ : Context α

lookupVar : (Γ : Context α) (x : NameIn α) → Type α
lookupVar ⌈⌉ x = nameInEmptyCase x
lookupVar (g , y ∶ s) x = raiseType (rezz _) (nameInBindCase x
  (λ q → lookupVar g (⟨ _ ⟩ q))
  (λ _ → s))
lookupVar (g , y ≔ u ∶ s) x = raiseType (rezz _) (nameInBindCase x
  (λ q → lookupVar g (⟨ _ ⟩ q))
  (λ _ → s))

{-# COMPILE AGDA2HS lookupVar #-}

rezzScope : (Γ : Context α) → Rezz α
rezzScope ⌈⌉ = rezz _
rezzScope (g , x ∶ _) =
  rezzCong (λ t → t <> (singleton x)) (rezzScope g)
rezzScope (g , x ≔ _ ∶ _) =
  rezzCong (λ t → t <> (singleton x)) (rezzScope g)
{-# COMPILE AGDA2HS rezzScope #-}

addContextTel : Context α → Telescope α rβ  → Context (extScope α rβ)
addContextTel {α} c ⌈⌉ =
  subst0 Context (sym extScopeEmpty) c
addContextTel {α} c (ExtendTel {rβ = rβ} x ty telt) =
  subst0 Context (sym extScopeBind) (addContextTel (c , x ∶ ty) telt)
{-# COMPILE AGDA2HS addContextTel #-}
