open import Scope

open import Utils.Either
open import Utils.Tactics using (auto)
open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Haskell.Law.Equality hiding (subst)
open import Haskell.Law.Monoid
open import Haskell.Prelude hiding (All; s; t)

open import Agda.Core.Name
open import Agda.Core.Utils
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Syntax
open import Agda.Core.Substitute

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

opaque
  MaybeLet : @0 Scope Name → Set
  MaybeLet α = (Maybe (Term α)) × Type α
  {-# COMPILE AGDA2HS MaybeLet #-}

  weakenMaybeLet : α ⊆ β → MaybeLet α → MaybeLet β
  weakenMaybeLet s (Nothing , ty) = (Nothing , weaken s ty)
  weakenMaybeLet s (Just u , ty) = (Just (weaken s u) , weaken s ty)
  {-# COMPILE AGDA2HS weakenMaybeLet #-}

  instance
    iWeakenMaybeLet : Weaken MaybeLet
    iWeakenMaybeLet .weaken = weakenMaybeLet
    {-# COMPILE AGDA2HS iWeakenMaybeLet #-}

  strengthenMaybeLet : α ⊆ β → MaybeLet β → Maybe (MaybeLet α)
  strengthenMaybeLet s (Nothing , ty) = do
    ty' ← strengthenType s ty
    return (Nothing , ty')
  strengthenMaybeLet s (Just u , ty) = do
    u' ← strengthen s u
    ty' ← strengthen s ty
    return (Just u' , ty')
  {-# COMPILE AGDA2HS strengthenMaybeLet #-}

  instance
    iStrengthenMaybeLet : Strengthen MaybeLet
    iStrengthenMaybeLet .strengthen = strengthenMaybeLet
    {-# COMPILE AGDA2HS iStrengthenMaybeLet #-}

  substMaybeLet : α ⇒ β → MaybeLet α → MaybeLet β
  substMaybeLet s (Nothing , ty) = (Nothing , subst s ty)
  substMaybeLet s (Just u , ty) = (Just (subst s u) , subst s ty)
  {-# COMPILE AGDA2HS substMaybeLet #-}

  instance
    iSubstMaybeLet : Substitute MaybeLet
    iSubstMaybeLet .subst = substMaybeLet
    {-# COMPILE AGDA2HS iSubstMaybeLet #-}


-- data CtxView : @0 Scope Name → Set where
--   CtxViewEmpty : CtxView mempty
--   CtxViewExtend : CtxView α → (@0 x : Name) → MaybeLet α → CtxView (α ▸ x)
-- {-# COMPILE AGDA2HS CtxView #-}

-- private opaque
--   unfolding MaybeLet
--   contextToCtxView : Context α → CtxView α
--   contextToCtxView ⌈⌉ = CtxViewEmpty
--   contextToCtxView (Γ , x ∶ ty) = CtxViewExtend (contextToCtxView Γ) x (Nothing , ty)
--   contextToCtxView (Γ , x ≔ u ∶ ty) = CtxViewExtend (contextToCtxView Γ) x (Just u , ty)

--   ctxViewToContext : CtxView α → Context α
--   ctxViewToContext CtxViewEmpty = ⌈⌉
--   ctxViewToContext (CtxViewExtend Γ x (Nothing , ty)) = ctxViewToContext Γ , x ∶ ty
--   ctxViewToContext (CtxViewExtend Γ x (Just u , ty)) = ctxViewToContext Γ , x ≔ u ∶ ty

--   equivLeft : (Γ : Context α) → ctxViewToContext (contextToCtxView Γ) ≡ Γ
--   equivLeft ⌈⌉ = refl
--   equivLeft (Γ , x ∶ ty) = cong (λ Γ₀ → Γ₀ , x ∶ ty) (equivLeft Γ)
--   equivLeft (Γ , x ≔ u ∶ ty) = cong (λ Γ₀ → Γ₀ , x ≔ u ∶ ty) (equivLeft Γ)

--   equivRight : (Γ : CtxView α) → contextToCtxView (ctxViewToContext Γ) ≡ Γ
--   equivRight CtxViewEmpty = refl
--   equivRight (CtxViewExtend Γ x (Nothing , ty)) = cong (λ Γ₀ → CtxViewExtend Γ₀ x (Nothing , ty)) (equivRight Γ)
--   equivRight (CtxViewExtend Γ x (Just u , ty)) = cong (λ Γ₀ → CtxViewExtend Γ₀ x (Just u , ty)) (equivRight Γ)

-- equivalenceContext : Equivalence (Context α) (CtxView α)
-- equivalenceContext = Equiv contextToCtxView ctxViewToContext equivLeft equivRight
-- {-# COMPILE AGDA2HS equivalenceContext #-}

-- rezzScope' : (Γ : CtxView α) → Rezz α
-- rezzScope' CtxViewEmpty = rezz _
-- rezzScope' (CtxViewExtend g x _) = rezzCong (λ t → t <> (singleton x)) (rezzScope' g)
-- {-# COMPILE AGDA2HS rezzScope' #-}
