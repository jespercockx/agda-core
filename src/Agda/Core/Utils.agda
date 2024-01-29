module Agda.Core.Utils where

open import Haskell.Prelude hiding (_,_)
open import Haskell.Extra.Refinement using (∃; _⟨_⟩)  public
open import Haskell.Extra.Erase      using (Σ0; ⟨_⟩_) public

-- we have 3 kinds of dependent pairs available,
-- encoding (x : a) (y : p x)

-- ∃  from Haskell.Extra.Refinement, which erases the snd component
-- Σ0 from Haskell.Extra.Erasure,    which erases the fst component
-- Σ  from this module,              which keeps both components

private module SigmaDef where
  
  record Sigma (a : Set) (b : @0 a → Set) : Set where
    constructor Pair
    field
      fst : a
      snd : b fst
  open Sigma public
  {-# COMPILE AGDA2HS Sigma #-}

-- this is done so as to have a valid Haskell constructor name
-- but be able to overload _,_ on the Agda side
open SigmaDef public renaming (Pair to infixr 5 _,_)

Σ = Sigma
{-# COMPILE AGDA2HS Σ inline #-}


-- we provide a shorthand syntax for all 3
------------------------------------------

infixr 2 ∃-syntax Σ Σ0-syntax

∃-syntax  = ∃
{-# COMPILE AGDA2HS ∃-syntax inline #-}

Σ0-syntax = Σ0
{-# COMPILE AGDA2HS Σ0-syntax inline #-}

syntax ∃-syntax  a (λ x → b) =  ∃[ x ∈ a ] b
syntax Σ0-syntax a (λ x → b) = Σ0[ x ∈ a ] b
syntax Σ         a (λ x → b) =  Σ[ x ∈ a ] b

pattern ∃⟨_⟩  x = x ⟨ _ ⟩
pattern Σ0⟨_⟩ x = ⟨ _ ⟩ x


map2 : {a : Set} {b c : @0 a → Set} (f : {x : a} → (b x → c x)) → Σ a b →  Σ a c
map2 f (av , bv) = av , f bv
{-# COMPILE AGDA2HS map2 #-}

-- TODO: move this upstream
subst' : (@0 p : @0 a → Set) {@0 x y : a} → @0 x ≡ y → p x → p y
subst' p refl z = z
{-# COMPILE AGDA2HS subst' transparent #-}

data Fuel : Set where
  None : Fuel
  More : Fuel → Fuel
{-# COMPILE AGDA2HS Fuel #-}
