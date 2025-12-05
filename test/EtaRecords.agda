module EtaRecords where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data Bool : Set where
  true : Bool
  false : Bool

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- record Pair (A B : Set) : Set where
--     no-eta-equality
--     field
--         fst : A
--         snd : B

-- x : Pair Nat Bool
-- x = record { fst = zero; snd = true }

-- y : Pair Nat Bool
-- y = record { fst = Pair.fst x; snd = Pair.snd x }

-- eta-R : {A B : Set} (x : Pair A B) → x ≡ record { fst = Pair.fst x ; snd = Pair.snd x }
-- eta-R r = {!!}

