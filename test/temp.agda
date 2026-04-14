data Bool : Set where
    True : Bool
    False : Bool

data Nat : Set where
  Zero : Nat
  Suc : Nat → Nat


data List (A : Set) : Set where 
    LNil : List A
    LCons : A → List A → List A

data Vector (A : Set) : Nat → Set where
  Nil : Vector A Zero
  Cons : {n : Nat} → A → Vector A n → Vector A (Suc n)

vectorBoolToList : {l : Nat} → Vector Bool l → List Nat
vectorBoolToList Nil = LNil
vectorBoolToList (Cons False vecSmaller) = LCons Zero (vectorBoolToList vecSmaller)
vectorBoolToList (Cons True vecSmaller) = LCons (Suc Zero) (vectorBoolToList vecSmaller)

data Container (param : Nat) : List Nat → Set where
    ContainerZero : Container param LNil
    ContainerAdd : (inp : Vector Bool param) → Container param (vectorBoolToList inp)


example0 : Container Zero LNil
example0 = ContainerZero

example1 : Container (Suc Zero) (LCons Zero LNil)
example1 = ContainerAdd (Cons False Nil)

-- Should return the param of Container param l
inspectParam : {param : Nat} {l : List Nat} → Container param l → Nat
inspectParam {param} _ = param



 

-- data Vector (A : Set) : (n : Nat) → Container n → Set where
--   Nil : Vector A Zero
--   Cons : {l : Nat} → A → Vector A l → Vector A (Suc l)