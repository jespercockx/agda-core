module UnitTypeChurch where

data Nat : Set where
    Zero : Nat
    Suc : Nat → Nat

data ⊤ : Set where
    * : ⊤

Id : (A : Set) (x : A) → A → Set₁
Id = λ A x y → (P : A → Set) → P x → P y

refl : (A : Set) (x : A) → Id A x x
refl = λ A x P p → p

const : (A : Set) → A → A → A
const = λ A → λ x → λ y → x

f : ⊤ 
f = *

g : ⊤
g = const ⊤ * *

eta_unit : Id ⊤ f g
eta_unit = refl ⊤ f
