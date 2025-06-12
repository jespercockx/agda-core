module SimpleDatatypes where

data ⊤ : Set where
  tt : ⊤

t : ⊤
t = tt

lambda⊤ : ⊤ → ⊤
lambda⊤ = λ _ → tt

case⊤ : ⊤ → ⊤
case⊤ _ =  tt

patternMatch⊤ : ⊤ → ⊤
patternMatch⊤ tt =  tt

data Bool : Set where
  true : Bool
  false : Bool

if : {A : Set} → Bool → A → A → A
if true  a _ = a
if false _ b = b


data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

left : (A B : Set) → A → A + B
left = λ A B x → inl x
