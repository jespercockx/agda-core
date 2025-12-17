module EtaFunctions where 

data Bool : Set where
  true : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

--data _≡_ {A : Set} (x : A) : A → Set where
--  refl : x ≡ x

--postulate
--  _≡_ : {A : Set} (x : A) → A → Set
--  refl : {A : Set} {x : A} → x ≡ x

Id : (A : Set) (x : A) → A → Set₁
Id = λ A x y → (P : A → Set) → P x → P y

refl : (A : Set) (x : A) → Id A x x
refl = λ A x P p → p

id_typ : Set → Set
id_typ = λ A → A

s : Set → Set
s = λ typ → id_typ typ

s' : (Set → Set) → Set → Set
s' = λ f → λ typ → f typ

id : (A : Set) → A → A
id = λ A x → x

idbool : Bool → Bool
idbool = λ b → b

addTwo : Nat → Nat
addTwo = λ x → (suc (suc x))

f : Nat → Nat
f = addTwo

g : Nat → Nat
g = λ x → addTwo x

z : (A B : Set) (f : A → B) → A → B
z = λ (A B : Set) h → λ a → (h a)

-- eta-functions : {A B : Set} (f : A → B) → (f ≡ (λ x → f x))
-- eta-functions = λ h → refl

eta-functions_expl : (A B : Set) (f : A → B) → (Id (A → B) f (λ x → f x))
eta-functions_expl = λ A B → λ f → refl (A → B) f

-- test : (A B : Set) (f : A → B) → Set
-- test = λ A B → λ f → A
