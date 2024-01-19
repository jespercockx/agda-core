open import Haskell.Prelude hiding ( All; m )
open import Haskell.Extra.Erase
open import Scope
open import Agda.Core.GlobalScope using (Globals)
import Agda.Core.Signature

module Agda.Core.TCM
    {@0 name    : Set}
    (@0 globals : Globals name)
    (open Agda.Core.Signature globals)
    (@0 sig     : Signature)
  where

open import Agda.Core.Syntax globals
open import Agda.Core.Reduce globals

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

record TCEnv : Set where
  constructor mkTCEnv
  field
    tcSignature : Rezz _ sig
    tcFuel      : Fuel
open TCEnv public

record TCM (a : Set) : Set where
  constructor mkTCM
  field
    runTCM : TCEnv → Either TCError a

tcmFuel : TCM Fuel
tcmFuel = mkTCM (λ f → Right (f .tcFuel))

tcmSignature : TCM (Rezz _ sig)
tcmSignature = mkTCM (λ f → Right (f .tcSignature))

fmapTCM : (a → b) → TCM a → TCM b
fmapTCM f (mkTCM runTCM) = mkTCM (fmap (fmap f) runTCM)

pureTCM : a → TCM a
pureTCM a = mkTCM (pure (pure a))

liftA2TCM : (a → b → c) → TCM a → TCM b → TCM c
liftA2TCM f (mkTCM ta) (mkTCM tb) = mkTCM (liftA2Env (liftA2Either f) ta tb)
  where
    liftA2Env : {a b c f : Set} → (a → b → c) → (f → a) → (f → b) → (f → c)
    liftA2Env f a b = f <$> a <*> b
    liftA2Either : {a b c e : Set} → (a → b → c) → Either e a → Either e b → Either e c
    liftA2Either f a b = f <$> a <*> b

bindTCM : TCM a → (a → TCM b) → TCM b
bindTCM ma mf = mkTCM (bindTCM' ma mf)
  where
  bindTCM' : TCM a → (a → TCM b) → TCEnv → Either TCError b
  bindTCM' (mkTCM ma) mf f with (ma f)
  ... | Left e = Left e
  ... | Right v = TCM.runTCM (mf v) f

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

liftEither : Either TCError a → TCM a
liftEither (Left e) = mkTCM λ f → Left e
liftEither (Right v) = mkTCM λ f → Right v

liftMaybe : Maybe a → TCError → TCM a
liftMaybe Nothing e = mkTCM λ f → Left e
liftMaybe (Just x) e = mkTCM λ f → Right x

tcError : TCError -> TCM a
tcError e = mkTCM λ f → Left e
