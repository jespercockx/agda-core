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
open import Agda.Core.Signature

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
  CtxExtend : Context α → (@0 x : Name) → Type α → Context (x ◃ α)

{-# COMPILE AGDA2HS Context #-}

_,_∶_ : Context α → (@0 x : Name) → Type α → Context (x ◃ α)
_,_∶_ = CtxExtend

infix 4 _,_∶_

{-# COMPILE AGDA2HS _,_∶_ inline #-}

private variable
  @0 Γ : Context α

lookupVar : (Γ : Context α) (x : NameIn α) → Type α
lookupVar CtxEmpty x = nameInEmptyCase x
lookupVar (CtxExtend g y s) x = raiseType (rezz _) (nameInBindCase x
  (λ _ → s)
  (λ q → lookupVar g (⟨ _ ⟩ q)))

{-# COMPILE AGDA2HS lookupVar #-}

rezzScope : (Γ : Context α) → Rezz α
rezzScope CtxEmpty = rezz _
rezzScope (CtxExtend g x _) =
  rezzCong (λ t → (singleton x) <> t) (rezzScope g)

{-# COMPILE AGDA2HS rezzScope #-}

addContextTel : Telescope α β → Context α → Context (~ β <> α)
addContextTel {α} EmptyTel c =
  subst0 Context
         (sym $ trans (cong (λ x → x <> α) revsIdentity)
                      (leftIdentity α))
         c
addContextTel {α} (ExtendTel {β = β} x ty telt) c =
  subst0 Context
         (trans (associativity (~ β) [ x ] α)
                (cong (λ t → t <> α) (sym $ revsBindComp β x)))
         (addContextTel telt (c , x ∶ ty))
{-# COMPILE AGDA2HS addContextTel #-}

addContextTypeS : Context α → TypeS α rβ → Context (extScope α rβ)
addContextTypeS Γ ⌈⌉ = Γ
addContextTypeS {α = α} Γ (YCons {rβ = rβ₀} {x = x} ty Δ) =
  let Γ' : Context (extScope (x ◃ α) rβ₀)
      Γ' = addContextTypeS (Γ , x ∶ weaken {!   !} ty) {! Δ !}
      in {!   !}
