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

addOne : Nat -> Nat
addOne = λ x → suc x

addTwo : Nat → Nat
addTwo = λ x → (suc (suc x))

addTwoAfterAddOne : Nat → Nat
addTwoAfterAddOne = λ x → (comp Nat Nat Nat addTwo addOne x)



eta-higher : (A B C : Set) → (f : A → B → C) → (λ x → λ y → f x y) ≡ f
eta-higher = λ A B C → λ f → refl

-- In this case, the type which Agda infers is addTwoAfterAddOne ≡ comp Nat Nat Nat addTwo addOne
-- So the agda-core typechecker would expand `addTwoAfterAddOne`, which expands to λ x → (comp Nat Nat Nat addTwo addOne x)
-- and the remaining equation would need to be solved by either eta-reduction or eta-expansion
eta-counterexample : addTwoAfterAddOne ≡ (λ x → (comp Nat Nat Nat addTwo addOne) x)
eta-counterexample = refl
