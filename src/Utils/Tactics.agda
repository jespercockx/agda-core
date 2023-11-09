module Utils.Tactics where

open import Haskell.Prelude hiding (_>>_; _>>=_)

import Agda.Builtin.String as BuiltinString
open import Agda.Builtin.Reflection public using ( Term ; TC )
open Agda.Builtin.Reflection renaming ( returnTC to return ; bindTC to _>>=_ )
  
private
  _>>_ : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → TC A → TC B → TC B
  m >> n = m >>= λ _ → n

  downFrom : Nat → List Nat
  downFrom (suc n) = suc n ∷ downFrom n
  downFrom zero = zero ∷ []

  -- NOTE(flupe): move upstream?
  instance
    iIsStringBuiltinString : IsString BuiltinString.String
    iIsStringBuiltinString .IsString.Constraint _ = ⊤
    iIsStringBuiltinString .fromString s = s

macro
  run : (Term → TC ⊤) → Term → TC ⊤
  run f hole = f hole

oneOf : ∀ {ℓ} {A : Set ℓ} → List (TC A) → TC A
oneOf [] = typeError []
oneOf (a ∷ as) = catchTC a (oneOf as)

-- A simple macro that tries to resolve the goal automatically.
-- Currently it just tries local variables and instances.

auto : Term → TC ⊤
auto hole = do
  hole ← reduce hole
  case hole of λ where
    (meta m _) → do
      let trySolution v = do
            debugPrint "auto" 10 (strErr "auto trying " ∷ termErr v ∷ [])
            unify hole v
      let debugSolutions vs = do
            `vs ← quoteTC vs
            debugPrint "auto" 10 (strErr "auto trying list " ∷ termErr `vs ∷ [])
      ctx ← getContext
      let vars = map (λ n → var n []) (downFrom (lengthNat ctx))
      debugSolutions vars
      catchTC (oneOf (map trySolution vars)) do
        debugPrint "auto" 10 (strErr "auto getting instances" ∷ [])
        cs ← getInstances m
        debugSolutions cs
        catchTC (oneOf (map trySolution cs)) do
          goal ← inferType hole
          typeError (strErr "auto could not find a value of type " ∷ termErr goal ∷ [])
    _ → typeError (strErr "auto called on already solved hole " ∷ termErr hole ∷ [])
