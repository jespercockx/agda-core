module EtaFunctions where 

data Bool : Set where
  true : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

id_typ : Set → Set
id_typ = λ A → A

s : Set → Set
s = λ typ → id_typ typ

s' : (Set → Set) → Set → Set
s' = λ f → λ typ → f typ

-- id : (A : Set) → A → A
-- id = λ A x → x

-- idbool : Bool → Bool
-- idbool = λ b → b

-- addTwo : Nat → Nat
-- addTwo = λ x → (suc (suc x))

-- f : Nat → Nat
-- f = addTwo

-- g : Nat → Nat
-- g = λ x → addTwo x

-- eta-functions : {A B : Set} (f : A → B) → (f ≡ (λ x → f x))
-- eta-functions = λ f → refl

eta-functions_expl : (A B : Set) (f : A → B) → (f ≡ (λ x → f x))
eta-functions_expl = λ A B → λ f → refl

test : (A B : Set) (f : A → B) → Set
test = λ A B → λ f → A
