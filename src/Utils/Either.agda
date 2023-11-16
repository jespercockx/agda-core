
open import Haskell.Prelude
  
module Utils.Either where

mapEither : (a → c) → (b → d) → (Either a b → Either c d)
mapEither f g = either (λ x → Left (f x)) (λ y → Right (g y))

mapLeft : (a → c) → (Either a b → Either c b)
mapLeft f = mapEither f id

mapRight : (b → d) → (Either a b → Either a d)
mapRight = mapEither id

swapEither : Either a b → Either b a
swapEither = either (λ x → Right x) (λ y → Left y)
