open import Zero
module One where

id : (A : Set) → A → A
id = λ A x → x

ap : (A B : Set) → (A → B) → A → B
ap = λ A B f x → f (id A x)

dap : (A : Set) (B : A → Set) → (∀ x → B x) → ∀ x → B x
dap = λ A B f x → f (id0 A x)
