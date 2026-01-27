data Bool : Set where
    True : Bool
    False : Bool

data Nat : Set where 
    Zero : Nat
    Suc : Nat → Nat

data List (A : Set) : Set where
    Nil : List A
    Cons : A → List A → List A

data Vector (A : Set) : Nat → Set where
    Nil : Vector A Zero
    Cons : (n : Nat) → A → Vector A n → Vector A (Suc n)

data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (x : A) → B x → Σ A B

-- 3 :: 4 :: nil
list1 : List Nat
list1 = Cons (Suc (Suc (Suc Zero))) (Cons (Suc (Suc (Suc (Suc Zero)))) Nil)

vector0 : Vector Nat Zero
vector0 = Nil

-- 2 :: nil
vector1 : Vector Nat (Suc Zero)
vector1 = Cons Zero ((Suc (Suc Zero))) Nil

deppair0 : Σ Nat (Vector Bool)
deppair0 = _,_ Zero Nil
