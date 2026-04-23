
data _≡_ (A : Set) (x : A) : (y : A) → Set where
    refl : _≡_ A x x

data Bool : Set where 
    True : Bool
    False : Bool


-- record Pair (A B : Set) : Set where
--     field
--         fst : A
--         snd : B

record ContainerRecord : Set where
    field
        theProj : Bool

record Σ (a : Set) (b : a → Set) : Set where
  field
    fst : a
    snd : b fst

const : (A : Set) → A → A → A
const = λ A → λ x → λ y → x

eta-R-one_fixed : (c : ContainerRecord) → 
    _≡_ ContainerRecord c (record { theProj = ContainerRecord.theProj c})
eta-R-one_fixed = λ c → refl

-- eta-R-two : (A B : Set) (p : Pair A B) → 
--   p ≡ record { fst = (const (Pair A B → A) Pair.fst Pair.fst) p ; snd = Pair.snd p }
-- eta-R-two = λ A B → λ p → refl

containerX : ContainerRecord
containerX = (ContainerRecord.constructor False)

data Nat : Set where
    Zero : Nat
    Suc : (base : Nat) → Nat

data Vector (A : Set) : (length : Nat) → Set where
    Nil : Vector A Zero
    Cons : {n : Nat} → (el : A) → (vecSmaller : Vector A n) → Vector A (Suc n)

sigmaRecordElement : Σ Nat (λ n → (Vector Bool n))
sigmaRecordElement = Σ.constructor (Suc (Suc Zero)) (Cons False (Cons False Nil))

sigmaRecordElementProjSnd : Vector Bool (Suc (Suc Zero))
sigmaRecordElementProjSnd = sigmaRecordElement .Σ.snd

