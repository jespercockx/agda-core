module EtaFunctionsChurch where 

-- data Bool : Set where
--   true : Bool
--   false : Bool

data Nat : Set where
  zero : Nat
  suc : Nat → Nat
  
-- an x of type A is equal to another element of type A,
-- if, for all predicates `P : A → Set`, if `P x` holds then `P y` also holds
-- The result of an `Id A x x` is a `Set₁`, because we are quantifying over all `Set`'s
Id : (A : Set) (x : A) → A → Set₁
Id = λ A x y → (P : A → Set) → P x → P y

refl : (A : Set) (x : A) → Id A x x
refl = λ A x P p → p

-- idbool : Bool → Bool
-- idbool = λ b → b

const : Nat → Nat → Nat
const = λ x → λ y → x

addOne : Nat → Nat
addOne = suc

-- Composition operator ∘
-- comp : (A B C : Set) → (B → C) → (A → B) → A → C
-- comp = λ (A B C : Set) → λ f → λ g → λ x → f (g x)

-- addTwo : Nat → Nat
-- addTwo = λ x → (suc (suc x))

-- addTwoAfterAddOne : Nat → Nat
-- addTwoAfterAddOne = λ x → (comp Nat Nat Nat addTwo addOne x)

-- eta-functions_expl : (A B : Set) (f : A → B) → (Id (A → B) f (λ x → f x))
-- eta-functions_expl = λ A B → λ f → refl (A → B) f

-- eta-functions_two : (A B C : Set) (f : B → C) → (g : A → B) → (Id (A → C) (comp A B C f g) (λ x → (comp A B C f g) x))
-- eta-functions_two = λ A B C → λ f → λ g → refl (A → C) (comp A B C f g)

-- apply : (A B : Set) → (A → B) → A → B
-- apply = λ A B → λ f → λ x → f x

-- eta-apply : (A B : Set) → (f : A → B) → Id (apply f) f

eta-functions_expl : (A B : Set) (f : A → B) → (Id (A → B) f (λ x → f x))
eta-functions_expl = λ A B → λ f → refl (A → B) f

-- eta-counterexample : Id (Nat → Nat) addTwoAfterAddOne (λ x → (comp Nat Nat Nat addTwo addOne) x)
-- eta-counterexample = refl (Nat → Nat) addTwoAfterAddOne

eta-counterexample-simple : Id (Nat → Nat) addOne (λ x → suc (const x x))
eta-counterexample-simple = refl (Nat → Nat) addOne

-- eta-higher : (A B C : Set) → (f : A → B → C) → Id (λ x → λ y → f x y) f
-- eta-higher = λ A B C → λ f → refl 