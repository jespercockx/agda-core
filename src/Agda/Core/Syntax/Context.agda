open import Haskell.Prelude           using (mempty; _<>_; _≡_; e)
open import Haskell.Extra.Erase       using (Rezz; rezz; rezzCong)
open import Haskell.Law.Monoid.Def    using (leftIdentity; rightIdentity)
open import Haskell.Law.Semigroup.Def using (associativity)
open import Haskell.Law.Equality      using (subst0; sym)

open import Agda.Core.Name
open import Agda.Core.Syntax.Term

module Agda.Core.Syntax.Context
  {{@0 globals : Globals}}
  where

private variable
  @0 x y     : Name
  @0 α       : Scope Name
  @0 rβ rγ   : RScope Name

---------------------------------------------------------------------------------------------------
                                          {- Context -}
---------------------------------------------------------------------------------------------------
data Context : @0 Scope Name → Set where
  CtxEmpty  : Context mempty
  CtxExtend : Context α → (@0 x : Name) → Type α → Context  (α ▸ x)

infix 4 _,_∶_
pattern _,_∶_ Γ x a = CtxExtend Γ x a

{-# COMPILE AGDA2HS Context #-}

rezzScope : (Γ : Context α) → Rezz α
rezzScope CtxEmpty = rezz _
rezzScope (CtxExtend g x _) =
  rezzCong (λ t → t <> (singleton x)) (rezzScope g)

{-# COMPILE AGDA2HS rezzScope #-}
---------------------------------------------------------------------------------------------------
                                        {- Telescopes -}
---------------------------------------------------------------------------------------------------
{- Telescopes are like contexts, mapping variables to types.
   Unlike contexts, they aren't closed.
   Telescope α β is like an extension of Context α with β.-}

data Telescope (@0 α : Scope Name) : @0 RScope Name → Set where
  EmptyTel  : Telescope α mempty
  ExtendTel : (@0 x : Name) → Type α → Telescope (α ▸ x) rβ  → Telescope α (x ◂ rβ)

pattern ⌈⌉ = EmptyTel
infix 6 _∶_◂_
pattern _∶_◂_ x t Δ = ExtendTel x t Δ

{-# COMPILE AGDA2HS Telescope #-}

rezzTel : Telescope α rβ → Rezz rβ
rezzTel ⌈⌉ = rezz _
rezzTel (x ∶ ty ◂ t) = rezzCong (λ t → x ◂ t) (rezzTel t)

{-# COMPILE AGDA2HS rezzTel #-}

opaque
  addTel : Telescope α rβ → Telescope (α ◂▸ rβ) rγ → Telescope α (rβ <> rγ)
  addTel ⌈⌉ tel0 =
    subst0 (λ α → Telescope α _) extScopeEmpty
    (subst0 (Telescope _) (sym (leftIdentity _)) tel0)
  addTel {α = α} {rγ = rγ} (x ∶  ty ◂ s) tel0 =
    subst0 (Telescope α) (associativity (x ◂) _ rγ)
    (x ∶ ty ◂ addTel s (subst0 (λ δ → Telescope δ rγ) extScopeBind tel0))
  {-# COMPILE AGDA2HS addTel #-}

opaque
  unfolding RScope

  caseTelEmpty : (tel : Telescope α mempty)
               → (@0 {{tel ≡ ⌈⌉}} → e)
               → e
  caseTelEmpty ⌈⌉ f = f

  caseTelBind : (tel : Telescope α (x ◂ rβ))
              → ((a : Type α) (rest : Telescope (α ▸ x) rβ) → @0 ⦃ tel ≡ ExtendTel x a rest ⦄ → e)
              → e
  caseTelBind  (_ ∶ a ◂ tel) f = f a tel

{-# COMPILE AGDA2HS caseTelEmpty #-}
{-# COMPILE AGDA2HS caseTelBind #-}

---------------------------------------------------------------------------------------------------
                                      {- Useful functions -}
---------------------------------------------------------------------------------------------------

addContextTel : Context α → Telescope α rβ  → Context (α ◂▸ rβ)
addContextTel c ⌈⌉ =
  subst0 Context (sym extScopeEmpty) c
addContextTel c (ExtendTel x ty telt) =
  subst0 Context (sym extScopeBind) (addContextTel (c , x ∶ ty) telt)
{-# COMPILE AGDA2HS addContextTel #-}
