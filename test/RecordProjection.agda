
data Nat : Set where
  Zero : Nat
  Suc : Nat → Nat

data Bool : Set where
  True : Bool
  False : Bool

data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x

const : (A : Set) → A → A → A
const = λ A → λ x → λ y → x

record Pair (A B : Set) : Set where
    field
        fst : A
        snd : B

x : Pair Nat Nat
x = record { fst = Zero; snd = Suc Zero }

proj_example1 : Nat
proj_example1 = Pair.fst x

proj_example2 : Bool
proj_example2 = (record { fst = Zero; snd = False }) .Pair.snd

proj_example3 : Bool
proj_example3 = (const (Pair Nat Bool) (record { fst = Zero; snd = False }) (record { fst = Zero; snd = False })) .Pair.snd


