module EtaRecordsUnit where

data Bool : Set where
    True : Bool
    False : Bool


data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x

record EmptyRecord : Set where
    constructor MkEmptyRecord

record EmptyRecord2 : Set where
    constructor MkEmptyRecord2


record ContainerRecord : Set where
    field
        theProj : Bool

test : (a b : EmptyRecord) → a ≡ b
test = λ a b → refl

-- Fails
-- testBad : (a : EmptyRecord) (b : EmptyRecord2) → a ≡ b
-- testBad = λ a b → refl


-- Fails
-- testBad2 : (a b : ContainerRecord) → a ≡ b
-- testBad2 = λ a b → refl
