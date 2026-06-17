module EtaRecordsUnit where

data Bool : Set where
    True : Bool
    False : Bool


data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x

record EmptyRecord : Set where
    constructor MkEmptyRecord


a : EmptyRecord
a = MkEmptyRecord

b : EmptyRecord
b = MkEmptyRecord

ex : a ≡ b
ex = refl

-- (atejandev): What does it even mean if one writes `record {}`? Does Agda infer that it means constructor of EmptyRecord?
-- eta_expand_empty_rec_two : (a : EmptyRecord) → (a ≡ record {})
-- eta_expand_empty_rec_two = λ a → refl

etaExpandEmptyRec : (a : EmptyRecord) → (a ≡ EmptyRecord.constructor)
etaExpandEmptyRec = λ a → refl

testUnitConvPositive : (a b : EmptyRecord) → a ≡ b
testUnitConvPositive = λ a b → refl
