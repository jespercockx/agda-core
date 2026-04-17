record Σ (a : Set) (b : a → Set) : Set where
  field
    fst : a
    snd : b fst

data Bool : Set where 
    True : Bool
    False : Bool

data Nat : Set where
    Zero : Nat
    Suc : Nat → Nat

data Vector (A : Set) : Nat → Set where
    Nil : Vector A Zero
    Cons : {n : Nat} → A → Vector A n → Vector A (Suc n)

sigmaRecordElement : Σ Nat (Vector Bool)
sigmaRecordElement = Σ.constructor (Suc (Suc Zero)) (Cons False (Cons False Nil))

sigmaRecordElementProjSnd : Vector Bool (Suc (Suc Zero))
sigmaRecordElementProjSnd = sigmaRecordElement .Σ.snd

