record Σ (a : Set) (b : a → Set) : Set where
  field
    fst : a
    snd : b fst

data Bool : Set where 
    True : Bool
    False : Bool

record ContainerRecord : Set where
    field
        theProj : Bool

data Nat : Set where
    Zero : Nat
    Suc : (base : Nat) → Nat

data Vector (A : Set) : (length : Nat) → Set where
    Nil : Vector A Zero
    Cons : {n : Nat} → (el : A) → (vecSmaller : Vector A n) → Vector A (Suc n)

sigmaRecordElement : Σ Nat (λ n → (Vector Bool n))
sigmaRecordElement = Σ.constructor (Suc (Suc Zero)) (Cons False (Cons False Nil))

sigmaRecordElementProjSnd : Vector Bool (Suc (Suc Zero))
sigmaRecordElementProjSnd = sigmaRecordElement .Σ.snd

