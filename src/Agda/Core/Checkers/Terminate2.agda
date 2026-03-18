open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Syntax.TerminationUtils
open import Agda.Core.Rules.Terminating2
module Agda.Core.Checkers.Terminate2
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where
private variable
  @0 x      : Name
  @0 α      : Scope Name
  @0 rβ     : RScope Name
  @0 u v    : Term α
  @0 a b c  : Type α
  @0 k l    : Sort α

private open module @0 G = Globals globals

findCycles : (p : Program) → CycleS p
findCycles p = CycleSNil
{-# COMPILE AGDA2HS findCycles #-}

postulate
  findCyclesComplete : (@0 p : Program) → @0 (TerminatingCycleS p (findCycles p)) → ((c : Cycle p) → TerminatingCycle p c)
{-# COMPILE AGDA2HS findCyclesComplete #-}

checkTerminatingCycle : (p : Program) → (c : Cycle p) → Either String (TerminatingCycle p c)
checkTerminatingCycle p c = Left "Not yet implemented" 

checkTerminating : (p : Program) → Either String (Terminating p)
checkTerminating p = mapRight
  (λ prf →   record {allCycles = (findCyclesComplete p prf)} )
  (go (findCycles p))
  where
    go : (cs : (CycleS p)) → Either String (TerminatingCycleS p cs)
    go CycleSNil = Right $ TerminatingCycleSNil
    go (CycleSCons c cs) =
      case checkTerminatingCycle p c of λ where
        (Left err) → Left err
        (Right pc) →
          case go cs of λ where
            (Left err) → Left err
            (Right pcs) → Right (TerminatingCycleSCons pc pcs)
{-# COMPILE AGDA2HS checkTerminating #-}

-- checkTerminating : (p : Program) (P : Cycle p → Set)
--                  → ((c : Cycle p) → Either String (P c))
--                  → Either String ((c : Cycle p) → P c)
-- checkTerminating p P decide = mapRight
--   (λ allPass c → allPass c (findCyclesComplete p c))
--   (go (findCycles p))
--   where
--     go : (cs : List (Cycle p)) → Either String ((c : Cycle p) → InList c cs → P c)
--     go [] = Right (λ c ())
--     go (c ∷ cs) = case decide c of λ where
--       (Left err)  → Left err
--       (Right pc)  → case go cs of λ where
--         (Left err)   → Left err
--         (Right pcs)  → Right (λ c' isin → helper c' isin pc pcs)
--           where
--             helper : (c' : Cycle p) → InList c' (c ∷ cs) → P c → ((c'' : Cycle p) → InList c'' cs → P c'') → P c'
--             helper c' (IsHead refl) pc' pcs' = pc'
--             helper c' (IsTail isin) pc' pcs' = pcs' c' isin
-- -- {-# COMPILE AGDA2HS checkTerminating #-}
