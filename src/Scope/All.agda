module Scope.All where

open import Haskell.Prelude hiding (All)

import Utils.List as List
open import Utils.Erase

open import Scope.Core
open import Scope.In
open import Scope.Sub
open import Scope.Split

private variable
  @0 name : Set
  @0 α β  : Scope name
  @0 x    : name
  p       : @0 name → Set

opaque
  unfolding Scope

  All : (p : @0 name → Set) → @0 Scope name → Set
  All p = List.All λ x → p (get x)
  {-# COMPILE AGDA2HS All #-}

  allEmpty : All p mempty
  allEmpty = List.ANil
  {-# COMPILE AGDA2HS allEmpty #-}

  allSingl : p x → All p [ x ]
  allSingl p = List.ACons p List.ANil
  {-# COMPILE AGDA2HS allSingl #-}

  getAllSingl : All p [ x ] → p x
  getAllSingl (List.ACons p List.ANil) = p
  {-# COMPILE AGDA2HS getAllSingl #-}

  allJoin : All p α → All p β → All p (α <> β)
  allJoin List.ANil pbs = pbs
  allJoin (List.ACons px pas) pbs = List.ACons px (allJoin pas pbs)
  {-# COMPILE AGDA2HS allJoin #-}

opaque
  unfolding All Sub Split

  lookupAll : All p α → x ∈ α → p x
  lookupAll ps                < EmptyR    > = getAllSingl ps
  lookupAll (List.ACons px _) < ConsL x _ > = px
  lookupAll (List.ACons _ ps) < ConsR x q > = lookupAll ps < q >
  {-# COMPILE AGDA2HS lookupAll #-}

{-

_!_ : {p : @0 name → Set} {@0 α : Scope name}
    → All p α → (@0 x : name) → {@(tactic auto) ok : x ∈ α} → p x
(ps ! _) {s} = lookupAll ps s

opaque
  unfolding All

  mapAll : (f : ∀ {@0 x} → P x → Q x) → All P α → All Q α
  mapAll f [] = []
  mapAll f (p ∷ ps) = f p ∷ mapAll f ps

  tabulateAll : {{Rezz α}} → (f : ∀ {@0 x} → (x ∈ α) → P x) → All P α
  tabulateAll {{rezz []}} f = []
  tabulateAll {{rezz (x ∷ α)}} f = f here ∷ tabulateAll {{rezz α}} (f ∘ there)
-}
