
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

-- result must be False
proj_example3 : Bool
proj_example3 = (const (Pair Nat Bool) (record { fst = Zero; snd = False }) (record { fst = Suc Zero; snd = True })) .Pair.snd

-- test_proj_example3 : proj_example3 ≡ False
-- test_proj_example3 = refl

-- Example with multiple usages of `fst` or `snd`
-- we'll take fst then snd so the result must be Suc Suc Zero
proj_example4 : Nat
proj_example4 = (const (Pair (Pair Nat Nat) Bool)
                  (record { fst = (record { fst = Suc (Suc (Suc Zero)); snd = Suc (Suc Zero)}); snd = True })
                  (record { fst = (record { fst = Zero; snd = Zero}); snd = False }) -- set all to zero, these values don't matter
                ) .Pair.fst .Pair.snd

-- test_proj_example4 : proj_example4 ≡ Suc (Suc Zero)
-- test_proj_example4 = refl

proj_example5 : Nat
proj_example5 = (const Nat 
                  (
                  (const (Pair Nat Nat)
                    (record { fst = Suc (Suc (Suc Zero)); snd = Suc (Suc Zero)})
                    (record { fst = Zero; snd = Zero})
                  ) .Pair.fst) 
                  (
                  (const (Pair Nat Nat) 
                    (record { fst = Zero; snd = Zero})
                    (record { fst = Zero; snd = Zero})
                  ) .Pair.snd
                  )
                )

test_proj_example5 : proj_example5 ≡ (Suc (Suc (Suc Zero)))
test_proj_example5 = refl
