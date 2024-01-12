module one where

data ⊤ : Set where
  tt : ⊤

t : ⊤
t = tt

id : (A : Set) → A → A
id = λ _ x → x

ap : (A B : Set) → (A → B) → A → B
ap = λ A _ f x → f (id A x)

dap : (A : Set) (B : A → Set) → (∀ x → B x) → ∀ x → B x
dap = λ A _ f x → f (id A x)
