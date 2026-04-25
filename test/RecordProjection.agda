
data Nat : Set where
  Zero : Nat
  Suc : Nat → Nat

-- data Bool : Set where
--   True : Bool
--   False : Bool

data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x

-- data _≡₁_ {A : Set₁} (x : A) : A → Set₂ where
--  refl₁ : x ≡₁ x


-- -- Agda Core does not support universe polymorphism, so this definition doesn't work
-- -- data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
-- --   refl : x ≡ x

-- const : (A : Set) → A → A → A
-- const = λ A → λ x → λ y → x

record Pair (A B : Set) : Set where
    field
        fst : A
        snd : B

-- record Pair₁ (A B : Set₁) : Set₂ where
--     field
--         fst₁ : A --fst₁ lives in Set₁
--         snd₁ : B --snd₁ lives in Set₁
-- --Thus, the overall Pair₁ lives in Set₂ 

-- record Σ (A : Set) (B : A → Set) : Set where
--   constructor _,_
--   field
--     fst : A
--     snd : B fst


-- pair_of_types : Pair₁ Set Set
-- pair_of_types = record { fst₁ = Nat; snd₁ = Bool }

-- x : Pair Nat Nat
-- x = record { fst = Zero; snd = Suc Zero }

-- TODO (atejandev): Uncomment this test once implicit arguments are correctly compiled
-- Pair_fst_alias : {A B : Set} → Pair A B → A
-- Pair_fst_alias = Pair.fst

Pair_fst_alias_expl_args : (A B : Set) → Pair A B → A
Pair_fst_alias_expl_args A B = Pair.fst {A}{B}

-- -- example for def where first argument is a projection function
-- proj_exampleDef1 : Nat
-- proj_exampleDef1 = x .Pair.fst

-- example for data where first argument is a projection function
proj_exampleData1 : _≡_ (Pair.fst {Nat}{Nat}) (Pair.fst {Nat}{Nat})
proj_exampleData1 = refl

-- universe_example : _≡₁_ (pair_of_types .Pair₁.fst₁) Nat
-- universe_example = refl₁


-- proj_example1 : Nat
-- proj_example1 = Pair.fst x

-- proj_example2 : Bool
-- proj_example2 = (record { fst = Zero; snd = False }) .Pair.snd

-- -- result must be False
-- proj_example3 : Bool
-- proj_example3 = (const (Pair Nat Bool) (record { fst = Zero; snd = False }) (record { fst = Suc Zero; snd = True })) .Pair.snd

-- -- test_proj_example3 : proj_example3 ≡ False
-- -- test_proj_example3 = refl

-- -- Example with multiple usages of `fst` or `snd`
-- -- we'll take fst then snd so the result must be Suc Suc Zero
-- proj_example4 : Nat
-- proj_example4 = (const (Pair (Pair Nat Nat) Bool)
--                   (record { fst = (record { fst = Suc (Suc (Suc Zero)); snd = Suc (Suc Zero)}); snd = True })
--                   (record { fst = (record { fst = Zero; snd = Zero}); snd = False }) -- set all to zero, these values don't matter
--                 ) .Pair.fst .Pair.snd

-- -- test_proj_example4 : proj_example4 ≡ Suc (Suc Zero)
-- -- test_proj_example4 = refl

-- proj_example5 : Nat
-- proj_example5 = (const Nat 
--                   (
--                   (const (Pair Nat Nat)
--                     (record { fst = Suc (Suc (Suc Zero)); snd = Suc (Suc Zero)})
--                     (record { fst = Zero; snd = Zero})
--                   ) .Pair.fst) 
--                   (
--                   (const (Pair Nat Nat) 
--                     (record { fst = Zero; snd = Zero})
--                     (record { fst = Zero; snd = Zero})
--                   ) .Pair.snd
--                   )
--                 )

-- test_proj_example5 : proj_example5 ≡ (Suc (Suc (Suc Zero)))
-- test_proj_example5 = refl
