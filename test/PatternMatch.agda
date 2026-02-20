module PatternMatch where

-- Basic natural numbers
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- foo : ℕ → ℕ
-- foo n = suc n

{-# NON_TERMINATING #-}
countdown : ℕ → ℕ
countdown zero = zero
countdown (suc n) = countdown n

babyackermann : ℕ → ℕ → ℕ
babyackermann zero n = suc n
babyackermann (suc m) zero = babyackermann m (suc zero)
babyackermann (suc m) (suc n) = babyackermann m (babyackermann zero n)

ackermann : ℕ → ℕ → ℕ
ackermann zero n = suc n
ackermann (suc m) zero = ackermann m (suc zero)
ackermann (suc m) (suc n) = ackermann m (ackermann (suc m) n)
--
-- -- NEGATIVE TEST: Should fail termination checker
{-# NON_TERMINATING #-}
loop : ℕ → ℕ
loop n = loop n

-- -- Helper: addition
-- _+_ : ℕ → ℕ → ℕ
-- zero + n = n
-- suc m + n = suc (m + n)

-- -- COMPLEX POSITIVE TEST 2: Mutual recursion with decreasing arguments
-- -- Both functions terminate because they call each other with strictly smaller arguments
-- even : ℕ → ℕ
-- odd  : ℕ → ℕ

-- even zero = suc zero  -- true (represented as 1)
-- even (suc n) = odd n

-- odd zero = zero  -- false (represented as 0)
-- odd (suc n) = even n

-- -- COMPLEX POSITIVE TEST 3: Multiple recursive calls, both on smaller arguments
-- fibonacci : ℕ → ℕ
-- fibonacci zero = zero
-- fibonacci (suc zero) = suc zero
-- fibonacci (suc (suc n)) = fibonacci (suc n) + fibonacci n



-- Alternative negative test: recursive call on same-sized argument
-- Uncomment to test - this will be rejected by Agda
-- {-# NON_TERMINATING #-}
-- bad-pred : ℕ → ℕ
-- bad-pred zero = zero
-- bad-pred (suc n) = bad-pred (suc n)
