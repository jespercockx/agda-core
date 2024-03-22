


module Agda.Core.TCMInstances where

open import Haskell.Prelude
open import Agda.Core.GlobalScope
open import Agda.Core.Signature
open import Agda.Core.TCM

private variable
  @0 name : Set
  @0 globals : Globals name
  @0 sig : Signature globals

private
  fmapTCM : (a → b) → TCM globals sig a → TCM globals sig b
  fmapTCM f = MkTCM ∘ fmap (fmap f) ∘ runTCM
  {-# COMPILE AGDA2HS fmapTCM #-}

  liftA2TCM : (a → b → c) → TCM globals sig a → TCM globals sig b → TCM globals sig c
  liftA2TCM g ta tb = MkTCM λ e → g <$> runTCM ta e <*> runTCM tb e
  {-# COMPILE AGDA2HS liftA2TCM #-}

  pureTCM : a → TCM globals sig a
  pureTCM = MkTCM ∘ const ∘ Right
  {-# COMPILE AGDA2HS pureTCM #-}

  bindTCM : TCM globals sig a → (a → TCM globals sig b) → TCM globals sig b
  bindTCM ma mf = MkTCM λ f → do v ← runTCM ma f ; runTCM (mf v) f
  {-# COMPILE AGDA2HS bindTCM #-}

instance
  iFunctorTCM : Functor (TCM globals sig)
  iFunctorTCM .fmap  = fmapTCM
  iFunctorTCM ._<$>_ = fmapTCM
  iFunctorTCM ._<&>_ = λ x f → fmapTCM f x
  iFunctorTCM ._<$_  = λ x m → fmapTCM (λ b → x {{b}}) m
  iFunctorTCM ._$>_  = λ m x → fmapTCM (λ b → x {{b}}) m
  iFunctorTCM .void  = fmapTCM (const tt)
  {-# COMPILE AGDA2HS iFunctorTCM #-}

instance
  iApplicativeTCM : Applicative (TCM globals sig)
  iApplicativeTCM .pure  = pureTCM
  iApplicativeTCM ._<*>_ = liftA2TCM id
  iApplicativeTCM ._<*_  = liftA2TCM (λ z _ → z)
  iApplicativeTCM ._*>_  = liftA2TCM (λ _ z → z)
  {-# COMPILE AGDA2HS iApplicativeTCM #-}

instance
  iMonadTCM : Monad (TCM globals sig)
  iMonadTCM ._>>=_  = bindTCM
  iMonadTCM .return = pureTCM
  iMonadTCM ._>>_   = λ x y → bindTCM x (λ z → y {{z}})
  iMonadTCM ._=<<_  = flip bindTCM
  {-# COMPILE AGDA2HS iMonadTCM #-}
