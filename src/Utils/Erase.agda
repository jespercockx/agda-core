module Utils.Erase where

  open import Agda.Primitive
  open import Agda.Builtin.Sigma
  open import Agda.Builtin.Equality
  open import Haskell.Prim hiding (a; b; c)

  private variable 
    ℓ′    : Level
    a b c : Set ℓ
    @0 x  : a
    @0 y  : b
    @0 xs : List a

  record Erase (@0 a : Set ℓ) : Set ℓ where
    constructor Erased
    field @0 get : a
  open Erase public
  {-# COMPILE AGDA2HS Erase #-}

  record Σ0 (@0 A : Set ℓ) (B : @0 A → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
    field
      @0 proj₁ : A
      proj₂ : B proj₁
  open Σ0 public
  {-# COMPILE AGDA2HS Σ0 unboxed #-}

  pattern <_> x = record { proj₁ = _ ; proj₂ = x }

  -- Resurrection of erased values
  record Rezz (a : Set ℓ) (@0 x : a) : Set ℓ where
    constructor Rezzed
    field
      rezzed    : a
      @0 isRezz : rezzed ≡ x
  open Rezz public
  {-# COMPILE AGDA2HS Rezz unboxed #-}

  pattern rezz x = Rezzed x refl

  instance
    rezz-id : {a : Set ℓ} {x : a} → Rezz a x
    rezz-id = rezz _

  rezzCong : (f : a → b) → Rezz a x → Rezz b (f x)
  rezzCong f (rezz x) = rezz (f x)
  {-# COMPILE AGDA2HS rezzCong #-}

  rezzCong2 : (f : a → b → c) → Rezz a x → Rezz b y → Rezz c (f x y)
  rezzCong2 f (rezz x) (rezz y) = rezz (f x y)
  {-# COMPILE AGDA2HS rezzCong2 #-}

  rezzHead : Rezz (List a) (x ∷ xs) → Rezz a x
  rezzHead (rezz (x ∷ xs)) = rezz x
  {-# COMPILE AGDA2HS rezzHead #-}

  rezzTail : Rezz (List a) (x ∷ xs) → Rezz (List a) xs
  rezzTail (rezz (x ∷ xs)) = rezz xs
  {-# COMPILE AGDA2HS rezzTail #-}

  rezzErase : Rezz (Erase a) (Erased x)
  rezzErase {x = x} = Rezzed (Erased x) refl

  {-# COMPILE AGDA2HS rezzErase #-}

  erase-injective : Erased x ≡ Erased y → x ≡ y
  erase-injective refl = refl

  inspect_by_ : (x : a) → (Rezz a x → b) → b
  inspect x by f = f (rezz x)
