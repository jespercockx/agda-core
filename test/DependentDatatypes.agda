module DependentDatatypes where

data Nat : Set where
  Zero : Nat
  Suc : Nat → Nat

data Vector (A : Set) : Nat → Set where
  Nil : Vector A Zero
  Cons : (n : Nat) → Vector A n → Vector A (Suc n)
