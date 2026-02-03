module EtaFunctions where

data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

-- postulate
--  _≡_ : {A : Set} (x : A) → A → Set
--  refl : {A : Set} {x : A} → x ≡ x

-- Composition operator ∘
comp : (A B C : Set) → (B → C) → (A → B) → A → C
comp = λ (A B C : Set) → λ f → λ g → λ x → f (g x)

const : {A : Set} → A → A → A
const = λ x → λ y → x

addOne : Nat → Nat
addOne = suc

addTwo : Nat → Nat
addTwo = λ x → (suc (suc x))

addTwoAfterAddOne : Nat → Nat
addTwoAfterAddOne = λ x → (comp Nat Nat Nat addTwo addOne x)

eta-higher : (A B C : Set) → (f : A → B → C) → (λ x → λ y → f (const x x) y) ≡ f
eta-higher = λ A B C → λ f → refl

eta-counterexample-simple : addOne ≡ (λ x → (suc (const x x)))
eta-counterexample-simple = refl

