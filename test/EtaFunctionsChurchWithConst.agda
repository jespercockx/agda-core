Id : (A : Set) (x : A) → A → Set₁
Id = λ A x y → (P : A → Set) → P x → P y

refl : (A : Set) (x : A) → Id A x x
refl = λ A x P p → p

const : (A : Set) → A → A → A
const = λ A → λ x → λ y → x

eta-functions_expl : (A B : Set) (f : A → B) → (Id (A → B) f (λ x → (f (const A x x))))
eta-functions_expl = λ A B → λ f → refl (A → B) f

eta-functions_two : (A B : Set) (f : A → B) → 
    (Id (A → B) (λ x → (f (const A x x))) (λ v → (λ w → (f w)) v) )
eta-functions_two = λ A B → λ f → refl (A → B) f

eta-functions_three : (A B : Set) (f : A → B) → 
    (Id (A → B) (λ v → (λ w → (f w)) v) (λ x → (f (const A x x))) )
eta-functions_three = λ A B → λ f → refl (A → B) f


