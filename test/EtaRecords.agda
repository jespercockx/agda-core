module EtaRecords where

data ⊥ : Set where
  --no constructor

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

record PairNoEta (A B : Set) : Set where
    no-eta-equality
    pattern
    field
        fstnoE : A
        sndnoE : B

record PairExplCon (A B : Set) : Set where 
    constructor _,_
    field
      fstE : A
      sndE : B

--example0 and example1 are both valid Agda epxressions
example0 : (A B : Set) → Set
example0 = Pair

example1 : (B : Set) → Set
example1 = Pair Nat

x : Pair Nat Nat
x = record { fst = Zero; snd = Suc Zero }

x' : Pair Nat Nat
x' = Pair.constructor Zero (Suc Zero)

proj_example : Nat
proj_example = Pair.fst x

-- y : Pair Nat Bool
-- y = record { fst = Pair.fst x; snd = False }

-- z : PairExplCon Nat Nat
-- z = _,_ Zero (Suc Zero)

-- eta-R-two : (A B : Set) (x : Pair A B) → 
--   x ≡ record { fst = (const (Pair A B → A) Pair.fst Pair.fst) x ; snd = Pair.snd x }
-- eta-R-two = λ A B → λ x → refl

-- eta-R-two-expl-con : (A B : Set) (x : PairExplCon A B) → 
--   x ≡ (_,_ (const (PairExplCon A B → A) PairExplCon.fstE PairExplCon.fstE x) (PairExplCon.sndE x))
-- eta-R-two-expl-con = λ A B → λ x → refl

-- eta-R-two : (A B : Set) (x : Pair A B) → 
--   x ≡ record { fst = (const (Pair A B → A) Pair.fst Pair.fst) x ; snd = Pair.snd x }
-- eta-R-two = λ A B → λ x → {!!}

-- (diode-lang): I don't think this statement is actually provable, because we have turned off eta-equality
-- eta-R-two_expl : (A B : Set) (x : PairNoEta A B) →
--   x ≡ record { fst = PairNoEta.fst x ; snd = PairNoEta.snd x }
-- eta-R-two_expl = λ A B → λ x → {!!}


