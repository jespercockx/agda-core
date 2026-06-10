module EtaRecords where
  
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

data PairAsData (A B : Set) : Set where
  PairAsDataConstructor : A → B → PairAsData A B


record PairExplCon (A B : Set) : Set where 
    constructor _,_
    field
      fstE : A
      sndE : B

x : Pair Nat Nat
x = record { fst = Zero; snd = Suc Zero }

xAsData : PairAsData Nat Nat
xAsData = PairAsDataConstructor Zero (Suc Zero)

x' : Pair Nat Nat
x' = Pair.constructor Zero (Suc Zero)

-- --example0 and example1 are both valid Agda epxressions
example0 : (A B : Set) → Set
example0 = Pair

example1 : (B : Set) → Set
example1 = Pair Nat


z : PairExplCon Nat Nat
z = _,_ Zero (Suc Zero)

record ContainerRecord : Set where
    field
        theProj : Bool

eta-R-one_fixed : (c : ContainerRecord) → 
    _≡_ c (record { theProj = ContainerRecord.theProj c})
eta-R-one_fixed = λ c → refl

--requirement for type checking eta-R-two
eta-R-two_sub : (A B : Set) → (const (Pair A B → A) Pair.fst Pair.fst) ≡ Pair.fst
eta-R-two_sub = λ A B → refl

-- -- (diode-lang):
-- -- keeping in mind Converter.agda, 
-- -- it should be that:
-- -- - rt = p
-- -- - rn = Pair
-- -- - argsTermS = [(const (Pair A B → A) Pair.fst Pair.fst) p; Pair.snd p]
eta-R-two : (A B : Set) (p : Pair A B) → 
  p ≡ record { fst = (const (Pair A B → A) Pair.fst Pair.fst) p ; snd = Pair.snd p }
eta-R-two = λ A B → λ p → refl
