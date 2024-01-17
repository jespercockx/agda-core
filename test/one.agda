module one where

data ⊤ : Set where
  tt : ⊤

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

t : ⊤
t = tt

left : (A B : Set) → A → A + B
left = λ A B x → inl x

id : (A : Set) → A → A
id = λ A x → x

ap : (A B : Set) → (A → B) → A → B
ap = λ A B f x → f (id A x)

dap : (A : Set) (B : A → Set) → (∀ x → B x) → ∀ x → B x
dap = λ A B f x → f (id A x)
