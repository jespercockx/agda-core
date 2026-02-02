module Implicit where

const : {A : Set} → A → A → A
const = λ x → λ y → x

eta-higher : (A B C : Set) → (f : A → B → C) → (λ x → λ y → f (const x x) y) ≡ f
eta-higher = λ A B C → λ f → refl

eta-counterexample-simple : addOne ≡ (λ x → (suc (const x x)))
eta-counterexample-simple = refl

