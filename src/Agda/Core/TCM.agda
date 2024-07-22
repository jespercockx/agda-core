open import Agda.Core.GlobalScope using (Globals; Name)
import Agda.Core.Signature as Signature

module Agda.Core.TCM
    (@0 globals : Globals)
    (open Signature globals)
    (@0 sig     : Signature)
  where

open import Scope
open import Agda.Core.Syntax globals as Syntax
open import Agda.Core.Reduce globals

open import Haskell.Prelude hiding (All; m)
open import Haskell.Extra.Erase using (Rezz; ⟨_⟩_)
open import Agda.Core.Utils using (Fuel; ∃-syntax; _⟨_⟩)

TCError = String

{-# COMPILE AGDA2HS TCError #-}

record TCEnv : Set where
  constructor MkTCEnv
  field
    tcSignature : Rezz _ sig
    tcFuel      : Fuel
open TCEnv public

{-# COMPILE AGDA2HS TCEnv #-}

record TCM (a : Set) : Set where
  constructor MkTCM
  field runTCM : TCEnv → Either TCError a
open TCM public

{-# COMPILE AGDA2HS TCM #-}

tcmFuel : TCM Fuel
tcmFuel = MkTCM (Right ∘ tcFuel)

{-# COMPILE AGDA2HS tcmFuel #-}

tcmSignature : TCM (Rezz _ sig)
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
