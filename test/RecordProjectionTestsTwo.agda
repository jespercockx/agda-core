
data Nat : Set where
  Zero : Nat
  Suc : Nat → Nat

data Bool : Set where
  True : Bool
  False : Bool

data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x

-- Agda Core does not support universe polymorphism, so this definition doesn't work
-- data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
--   refl : x ≡ x


data _≡₁_ {A : Set₁} (x : A) : A → Set₂ where
 refl₁ : x ≡₁ x

record Pair (A B : Set) : Set where
    field
        fst : A
        snd : B

record Pair₁ (A B : Set₁) : Set₂ where
    field
        fst₁ : A --fst₁ lives in Set₁
        snd₁ : B --snd₁ lives in Set₁
--Thus, the overall Pair₁ lives in Set₂ 

pair_of_types : Pair₁ Set Set
pair_of_types = record { fst₁ = Nat; snd₁ = Bool }

--x does not make use of projection
x : Pair Nat Nat
x = record { fst = Zero; snd = Suc Zero }

-- example for def where first argument is a projection function
proj_exampleDef1 : Nat
proj_exampleDef1 = x .Pair.fst

-- example for data where first argument is a projection function
proj_exampleData1 : _≡_ (Pair.fst {Nat}{Nat}) (Pair.fst {Nat}{Nat})
proj_exampleData1 = refl

-- example for record where first argumnt is a record projection
proj_exampleRec1 : Pair (Pair Nat Nat → Nat) Bool
proj_exampleRec1 = record { fst = Pair.fst {Nat}{Nat}; snd = False}

universe_example : _≡₁_ (pair_of_types .Pair₁.fst₁) Nat
universe_example = refl₁

