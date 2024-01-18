module Agda.Core.TCM where

open import Haskell.Prelude
open import Haskell.Extra.Delay

module Pair where
  open import Agda.Primitive
  private variable
    ℓ ℓ′ : Level
  
  record Pair (a : Set ℓ) (p : (@0 _ : a) → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
    constructor MkPair
    field
      pfst : a
      psnd : p pfst
  open Pair public
  {-# COMPILE AGDA2HS Pair #-}

open Pair

pattern _⟨_⟩ a b = MkPair a b

infix 4 ∃
∃ : (a : Set) (p : @0 a → Set) → Set
∃ a p = Pair a p
{-# COMPILE AGDA2HS ∃ inline #-}

TCError = String

record TCM (a : Set) : Set where
  constructor mkTCM
  field
    runTCM : Delay (Either TCError a) ∞

fmapTCM : (a → b) → TCM a → TCM b
fmapTCM f (mkTCM runTCM) = mkTCM (fmap (fmap f) runTCM)

pureTCM : a → TCM a
pureTCM a = mkTCM (pure (pure a))

liftA2TCM : (a → b → c) → TCM a → TCM b → TCM c
liftA2TCM f (mkTCM ta) (mkTCM tb) = mkTCM (liftA2Delay (liftA2Either f) ta tb)
  where
    liftA2Delay : {a b c : Set} → (a → b → c) → Delay a ∞ → Delay b ∞ → Delay c ∞
    liftA2Delay f a b = f <$> a <*> b
    liftA2Either : {a b c e : Set} → (a → b → c) → Either e a → Either e b → Either e c
    liftA2Either f a b = f <$> a <*> b

{-# TERMINATING #-}
bindTCM : TCM a → (a → TCM b) → TCM b
bindTCM (mkTCM (now (Left x))) mf = mkTCM (now (Left x))
bindTCM (mkTCM (now (Right x))) mf = mf x
bindTCM (mkTCM (later x)) mf = bindTCM (mkTCM (force x)) mf

instance
  iFunctorTCM : Functor TCM
  Functor.fmap iFunctorTCM = fmapTCM
  Functor._<$>_ iFunctorTCM = fmapTCM
  Functor._<&>_ iFunctorTCM = λ x f → fmapTCM f x
  Functor._<$_ iFunctorTCM = λ x m → fmapTCM (λ b → x {{b}}) m
  Functor._$>_ iFunctorTCM = λ m x → fmapTCM (λ b → x {{b}}) m
  Functor.void iFunctorTCM = fmapTCM (const tt)

  iApplicativeTCM : Applicative TCM
  Applicative.pure iApplicativeTCM = pureTCM
  Applicative._<*>_ iApplicativeTCM = liftA2TCM id
  Applicative.super iApplicativeTCM = iFunctorTCM
  Applicative._<*_ iApplicativeTCM = liftA2TCM (λ z _ → z)
  Applicative._*>_ iApplicativeTCM = liftA2TCM (λ _ z → z)

  iMonadTCM : Monad TCM
  Monad._>>=_ iMonadTCM = bindTCM
  Monad.super iMonadTCM = iApplicativeTCM
  Monad.return iMonadTCM = pureTCM
  Monad._>>_ iMonadTCM = λ m m₁ → bindTCM m (λ x → m₁ {{x}})
  Monad._=<<_ iMonadTCM = flip bindTCM

liftDelay : Delay a ∞ → TCM a
liftDelay (now x) = mkTCM (now (Right x))
liftDelay (later x) = mkTCM (fmap Right (force x))

liftEither : Either TCError a → TCM a
liftEither e = mkTCM (now e)

liftMaybe : Maybe a → TCError → TCM a
liftMaybe Nothing e = mkTCM (now (Left e))
liftMaybe (Just x) e = mkTCM (now (Right x))

tcError : TCError -> TCM a
tcError e = mkTCM (now (Left e))
