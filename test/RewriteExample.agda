module RewriteExample where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate P : Nat → Set
postulate plus-commute : (a b : Nat) → a + b ≡ b + a

thm : (a b : Nat) → P (a + b) → P (b + a)
thm a b t with a + b       | plus-commute a b
thm a b t   |  .(b + a)    | refl             = t

thmRewrite : (a b : Nat) → P (a + b) → P (b + a)
thmRewrite a b t rewrite (plus-commute a b) = t