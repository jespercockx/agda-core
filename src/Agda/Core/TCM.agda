
open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Signature
open import Scope

open import Haskell.Prelude hiding (All; m)
open import Haskell.Extra.Erase using (Rezz; rezz; ⟨_⟩_)
open import Agda.Core.Utils using (Fuel; ∃-syntax; _⟨_⟩; Instance; I)

module Agda.Core.TCM
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

TCError = String

{-# COMPILE AGDA2HS TCError #-}

record TCEnv : Set where
  constructor MkTCEnv
  field
    tcSignature : Rezz sig
    tcFuel      : Fuel
open TCEnv public

{-# COMPILE AGDA2HS TCEnv #-}

record TCM (a : Set) : Set where
  constructor MkTCM
  field runTCM : TCEnv → Either TCError a
open TCM public

{-# COMPILE AGDA2HS TCM #-}

tcmFuel : TCM (Instance Fuel)
tcmFuel = MkTCM (Right ∘ (λ x → I {{x}}) ∘ tcFuel)

{-# COMPILE AGDA2HS tcmFuel #-}

tcmSignature : TCM (Rezz sig)
tcmSignature = MkTCM (Right ∘ tcSignature)

{-# COMPILE AGDA2HS tcmSignature #-}

tcError : TCError -> TCM a
tcError = MkTCM ∘ const ∘ Left
{-# COMPILE AGDA2HS tcError #-}

assert : Bool → TCError → TCM ⊤
assert False e = tcError e
assert True e = MkTCM (const (Right tt))
{-# COMPILE AGDA2HS assert #-}

liftEither : Either TCError a → TCM a
liftEither (Left e) = MkTCM λ f → Left e
liftEither (Right v) = MkTCM λ f → Right v

{-# COMPILE AGDA2HS liftEither #-}

liftMaybe : Maybe a → TCError → TCM a
liftMaybe Nothing e = MkTCM λ f → Left e
liftMaybe (Just x) e = MkTCM λ f → Right x

{-# COMPILE AGDA2HS liftMaybe #-}
