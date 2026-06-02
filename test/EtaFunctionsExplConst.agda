module EtaFunctionsExplConst where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

-- postulate
--  _≡_ : {A : Set} (x : A) → A → Set
--  refl : {A : Set} {x : A} → x ≡ x

const : (A : Set) → A → A → A
const = λ A → λ x → λ y → x

addOne : Nat → Nat
addOne = suc

addTwo : Nat → Nat
addTwo = λ x → (suc (suc x))

eta-functions_expl' : (A B : Set) (f : A → B) → (f ≡ (λ x → (f (const A x x))))
eta-functions_expl' = λ A B → λ f → refl

eta-app-1 : (f : Nat -> Nat -> Nat) -> (λ x -> (f zero x)) ≡ (f (const Nat zero (suc zero)))
eta-app-1 = λ f → refl

eta-functions_expl'_reversed : (A B : Set) (f : A → B) → ((λ x → (f (const A x x))) ≡ f)
eta-functions_expl'_reversed = λ A B → λ f → refl

eta-functions_two : (A B : Set) (f : A → B) → 
    ((λ x → (f (const A x x))) ≡ (λ v → (λ w → (f w)) v) )
eta-functions_two = λ A B → λ f → refl

eta-functions_three : (A B : Set) (f : A → B) → 
    ((λ v → (λ w → (f w)) v) ≡ (λ x → (f (const A x x))) )
eta-functions_three = λ A B → λ f → refl

eta-functions_four : (A B : Set) (f : A → B) → 
    ((λ v → (λ w → (f (const A w w))) (const A v v)) ≡ f)
eta-functions_four = λ A B → λ f → refl

eta-higher : (A B C : Set) → (f : A → B → C) → (λ x → λ y → f (const A x x) y) ≡ f
eta-higher = λ A B C → λ f → refl

eta-counterexample-2 : addOne ≡ (λ x → (suc (const Nat x x)))
eta-counterexample-2 = refl
