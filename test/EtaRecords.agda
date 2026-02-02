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
        fst : A
        snd : B

record PairExplCon (A B : Set) : Set where 
    constructor _,_
    field
      fst : A
      snd : B

x : Pair Nat Nat
x = record { fst = Zero; snd = Suc Zero }

x' : Pair Nat Nat
x' = Pair.constructor Zero (Suc Zero)

y : Pair Nat Bool
y = record { fst = Pair.fst x; snd = False }

z : PairExplCon Nat Nat
z = _,_ Zero (Suc Zero)

-- (diode-lang): I don't think this statement is actually provable, because we have turned off eta-equality
-- eta-R-two_expl : (A B : Set) (x : PairNoEta A B) →
--   x ≡ record { fst = PairNoEta.fst x ; snd = PairNoEta.snd x }
-- eta-R-two_expl = λ A B → λ x → {!!}


eta-R-two : (A B : Set) (x : Pair A B) → 
  x ≡ record { fst = (const (Pair A B → A) Pair.fst Pair.fst) x ; snd = Pair.snd x }
eta-R-two = λ A B → λ x → refl

eta-R-two-expl-con : (A B : Set) (x : PairExplCon A B) → 
  x ≡ (_,_ (const (PairExplCon A B → A) PairExplCon.fst PairExplCon.fst x) (PairExplCon.snd x))
eta-R-two-expl-con = λ A B → λ x → refl

-- eta-R-two : (A B : Set) (x : Pair A B) → 
--   x ≡ record { fst = (const (Pair A B → A) Pair.fst Pair.fst) x ; snd = Pair.snd x }
-- eta-R-two = λ A B → λ x → {!!}

