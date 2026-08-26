module TRecTypechecking where 

data Bool : Set where
  True : Bool
  False : Bool

data Nat : Set where
  Zero : Nat
  Suc : Nat → Nat

record Pair (A B : Set) : Set where
    field
        fst : A
        snd : B

TRec_example1 : Set
TRec_example1 = Pair Nat Nat

TRec_example2 : Set
TRec_example2 = Pair Bool Nat
