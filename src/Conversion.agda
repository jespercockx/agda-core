open import Scope.Core
open import Scope.Split
open import Scope.Sub
open import Scope.In
open import Scope.All

open import Haskell.Extra.Dec
open import Utils.Either
open import Haskell.Extra.Erase
open import Haskell.Extra.Loop

open import Haskell.Prelude hiding (All; a; b; c; t)

import Syntax

module Conversion
  {@0 name  : Set}
  (@0 defs     : Scope name)
  (@0 cons     : Scope name)
  (@0 conArity : All (λ _ → Scope name) cons)
  (@0 defType  : All (λ _ → Syntax.Type defs cons conArity mempty) defs)
  where

open Syntax defs cons conArity
open import Substitute defs cons conArity
open import Reduce defs cons conArity
open import Context defs cons conArity

private variable
  @0 x y z : name
  @0 α β γ : Scope name
  @0 t t' u u' v v' : Term α
  @0 k l n : Sort α
  @0 a a' b b' c c' : Type α
  @0 w w' : Elim α

data Conv (@0 Γ : Context α) : @0 Type α → @0 Term α → @0 Term α → Set
data ConvElim (@0 Γ : Context α) : @0 Type α → @0 Term α → @0 Elim α → @0 Elim α → Set

renameTop : Rezz _ α → Term (x ◃ α) → Term (y ◃ α)
renameTop {x = x} {y = y} r = substTerm (liftBindSubst {x = x} {y = y} (idSubst r))
{-# COMPILE AGDA2HS renameTop #-}

@0 renameTopE : Term (x ◃ α) → Term (y ◃ α)
renameTopE = renameTop (rezz _)

syntax Conv Γ t x y = Γ ⊢ x ≅ y ∶ t
syntax ConvElim Γ t x e₁ e₂ = Γ ⊢ x [ e₁ ≅ e₂ ] ∶ t

data Conv {α} Γ where
  CRefl  : Γ ⊢ u ≅ u ∶ t

  CLam   : (Γ , x ∶ a) ⊢ renameTopE u ≅ renameTopE v ∶ b
         → Γ ⊢ TLam y u ≅ TLam z v ∶ TPi x k l a b

  CPi    : Γ ⊢ a ≅ a' ∶ TSort k
         → (Γ , x ∶ a) ⊢ b ≅ (renameTopE b') ∶ TSort (weakenSort (subWeaken subRefl) l)
         → Γ ⊢ (TPi x k l a b) ≅ (TPi y k l a' b') ∶ TSort (funSort k l)

  CApp   : Γ ⊢ u ≅ u' ∶ a
         → Γ ⊢ u [ w ≅ w' ] ∶ a
         -- Note: We assume all terms are well-typed, so we allow any type b here
         → Γ ⊢ TApp u w ≅ TApp u' w' ∶ b

  CRedT  : (@0 fuel : _)
         → Γ ⊢ u ≅ v ∶ reduce (rezz _) t fuel
         → Γ ⊢ u ≅ v ∶ t

  CRedL  : (@0 fuel : _)
         → Γ ⊢ reduce (rezz _) u fuel ≅ v ∶ t
         → Γ ⊢ u ≅ v ∶ t

  CRedR  : (@0 fuel : _)
         → Γ ⊢ u ≅ reduce (rezz _) v fuel ∶ t
         → Γ ⊢ u ≅ v ∶ t

{-# COMPILE AGDA2HS Conv #-}

data ConvElim Γ where
  CERedT : (@0 fuel : _)
         → Γ ⊢ u [ w ≅ w' ] ∶ reduce (rezz _) t fuel
         → Γ ⊢ u [ w ≅ w' ] ∶ t

  CEArg  : Γ ⊢ v ≅ v' ∶ a
         → Γ ⊢ u [ EArg v ≅ EArg v' ] ∶ TPi x k l a b
  -- TODO: CEProj : {!   !}
  -- TODO: CECase : {!   !}

{-# COMPILE AGDA2HS ConvElim #-}
