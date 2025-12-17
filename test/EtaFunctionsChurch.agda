module EtaFunctionsChurch where 

data Bool : Set where
  true : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc : Nat → Nat
  

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

-- Composition operator ∘
comp : (A B C : Set) → (B → C) → (A → B) → A → C
comp = λ (A B C : Set) → λ f → λ g → λ x → f (g x)

addOne : Nat -> Nat
addOne = λ x → suc x

addTwo : Nat → Nat
addTwo = λ x → (suc (suc x))

addTwoAfterAddOne : Nat → Nat
addTwoAfterAddOne = λ x → (comp Nat Nat Nat addTwo addOne x)


-- eta-functions : {A B : Set} (f : A → B) → (f ≡ (λ x → f x))
-- eta-functions = λ h → refl

eta-functions_expl : (A B : Set) (f : A → B) → (Id (A → B) f (λ x → f x))
eta-functions_expl = λ A B → λ f → refl (A → B) f

eta-functions_two : (A B C : Set) (f : B → C) → (g : A → B) → (Id (A → C) (comp A B C f g) (λ x → (comp A B C f g) x))
eta-functions_two = λ A B C → λ f → λ g → refl (A → C) (comp A B C f g)


test : Id addTwoAfterAddOne (λ x → (comp Nat Nat Nat addTwo addOne) x)
test = refl

-- eta-higher : (A B C : Set) → (f : A → B → C) → Id (λ x → λ y → f x y) f
-- eta-higher = λ A B C → λ f → refl 