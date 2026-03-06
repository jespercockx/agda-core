module EtaUnit where

data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

data ⊤ : Set where
    * : ⊤

test : (a b : ⊤) → a ≡ b
test = λ a b → refl

-- Singleton : Set → Set
-- Singleton A = (x y : A) → x ≡ y

-- test : Singleton ⊤
-- test = λ x y → refl


