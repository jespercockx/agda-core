module EtaRecordsUnit where

data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x

record EmptyRecord : Set where
    constructor MkEmptyRecord

test : (a b : EmptyRecord) → a ≡ b
test = λ a b → refl