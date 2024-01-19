open import Agda.Core.GlobalScope using (Globals)
open import Agda.Core.Signature   using (Signature)

module Agda.Core.TCM
    {@0 name    : Set}
    (@0 globals : Globals name)
    (@0 sig     : Signature globals)
  where

open import Haskell.Prelude hiding (All; m)
open import Haskell.Extra.Erase using (Rezz)
open import Agda.Core.Utils     using (Fuel)

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

private
  fmapTCM : (a → b) → TCM a → TCM b
  fmapTCM f = MkTCM ∘ fmap (fmap f) ∘ runTCM
  {-# COMPILE AGDA2HS fmapTCM #-}

  liftA2TCM : (a → b → c) → TCM a → TCM b → TCM c
  liftA2TCM g ta tb = MkTCM λ e → g <$> runTCM ta e <*> runTCM tb e
  {-# COMPILE AGDA2HS liftA2TCM #-}

  pureTCM : a → TCM a
  pureTCM = MkTCM ∘ const ∘ Right
  {-# COMPILE AGDA2HS pureTCM #-}

  bindTCM : TCM a → (a → TCM b) → TCM b
  bindTCM ma mf = MkTCM λ f → do v ← runTCM ma f ; runTCM (mf v) f
  {-# COMPILE AGDA2HS bindTCM #-}

instance
  iFunctorTCM : Functor TCM
  iFunctorTCM .fmap  = fmapTCM
  iFunctorTCM ._<$>_ = fmapTCM
  iFunctorTCM ._<&>_ = λ x f → fmapTCM f x
  iFunctorTCM ._<$_  = λ x m → fmapTCM (λ b → x {{b}}) m
  iFunctorTCM ._$>_  = λ m x → fmapTCM (λ b → x {{b}}) m
  iFunctorTCM .void  = fmapTCM (const tt)
  {-# COMPILE AGDA2HS iFunctorTCM #-}

instance
  iApplicativeTCM : Applicative TCM
  iApplicativeTCM .pure  = pureTCM
  iApplicativeTCM ._<*>_ = liftA2TCM id
  iApplicativeTCM ._<*_  = liftA2TCM (λ z _ → z)
  iApplicativeTCM ._*>_  = liftA2TCM (λ _ z → z)
  {-# COMPILE AGDA2HS iApplicativeTCM #-}

instance
  iMonadTCM : Monad TCM
  iMonadTCM ._>>=_  = bindTCM
  iMonadTCM .return = pureTCM
  iMonadTCM ._>>_   = λ x y → bindTCM x (λ z → y {{z}})
  iMonadTCM ._=<<_  = flip bindTCM
  {-# COMPILE AGDA2HS iMonadTCM #-}

liftEither : Either TCError a → TCM a
liftEither (Left e) = MkTCM λ f → Left e
liftEither (Right v) = MkTCM λ f → Right v

{-# COMPILE AGDA2HS liftEither #-}

liftMaybe : Maybe a → TCError → TCM a
liftMaybe Nothing e = MkTCM λ f → Left e
liftMaybe (Just x) e = MkTCM λ f → Right x

{-# COMPILE AGDA2HS liftMaybe #-}
