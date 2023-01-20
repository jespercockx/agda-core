-- Some general definitions

module Utils where

open import Agda.Primitive

variable
  @0 a b c d ℓ : Level
  @0 A B C D : Set ℓ
  @0 P Q R : A → Set ℓ
  @0 x y z x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : A  
  @0 α α₁ α₂ β β₁ β₂ γ γ₁ γ₂ δ δ₁ δ₂ ε ε₁ ε₂ ζ ζ₁ ζ₂ : A
  @0 f g h : A → B

id : A → A
id x = x

const : A → B → A
const x _ = x

infixr 9 _∘_
_∘_ : ∀ {@0 A : Set a} {@0 B : A → Set b} {@0 C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

module Bottom where
  open import Data.Empty as Empty public using (⊥)

  ⊥-elim : @0 ⊥ → A
  ⊥-elim ()

open Bottom public using (⊥; ⊥-elim)

open import Data.Unit as Unit public using (⊤; tt)

open import Data.String.Base as String public using (String)

module Product where

  record Σ (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁
  open Σ public

  infixr 8 _,_

  _×_ : Set a → Set b → Set (a ⊔ b)
  A × B = Σ A (λ _ → B)

  infixr 5 _×_

  map₂ : (f : ∀ {x} → P x → Q x) → Σ A P → Σ A Q
  map₂ f (x , y) = (x , f y)

  curry : {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c}
        → ((x : A) (y : B x) → C x y)
        → ((x , y) : Σ A B) → C x y
  curry f (x , y) = f x y

  uncurry : {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c}
          → (((x , y) : Σ A B) → C x y)
          → (x : A) (y : B x) → C x y
  uncurry f x y = f (x , y)

open Product public using (Σ; _×_; _,_; proj₁; proj₂; curry; uncurry)

module Equality where

  open import Relation.Binary.PropositionalEquality.Core public using (_≡_; refl)

  sym : x ≡ y → y ≡ x
  sym refl = refl

  infix 5 _∎
  infixr 4 _≡⟨_⟩_

  _∎ : (@0 x : A) → x ≡ x
  _ ∎ = refl

  _≡⟨_⟩_ : (@0 x : A) → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ refl ⟩ eq = eq

  cong : (@0 f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  cong₂ : (@0 f : A → B → C) → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
  cong₂ f refl refl = refl

  subst : (@0 P : A → Set ℓ) → @0 x ≡ y → P x → P y
  subst P refl x = x

  UIP : {p q : x ≡ y} → p ≡ q
  UIP {p = refl} {q = refl} = refl

  -- Note: cannot erase levels and types here because built-in equality requires them to be non-erased.
  PathOver : ∀ {a} {ℓ} {A : Set a} (P : A → Set ℓ) {x y : A} (eq : x ≡ y) → P x → P y → Set ℓ
  PathOver P refl px py = px ≡ py

  dcong : (f : (x : A) → P x) (eq : x ≡ y) → PathOver P eq (f x) (f y)
  dcong f refl = refl

  dcong₂ : {A : Set a} {B : A → Set b} {C : Set c}
         → (f : (x : A) (y : B x) → C)
         → {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂}
         → (x= : x₁ ≡ x₂) (y= : PathOver B x= y₁ y₂) → f x₁ y₁ ≡ f x₂ y₂
  dcong₂ f refl refl = refl

open Equality public

module Equivalence where

  record IsEquiv {A : Set a} {B : Set b} (f : A → B) : Set (a ⊔ b) where
    field
      inv : B → A
      left-inverse : (x : A) → inv (f x) ≡ x
      right-inverse : (y : B) → f (inv y) ≡ y
      left-right : (x : A) → cong f (left-inverse x) ≡ right-inverse (f x)
  open IsEquiv public

  _≃_ : Set a → Set b → Set (a ⊔ b)
  A ≃ B = Σ (A → B) IsEquiv

  isEquiv : {f : A → B} (g : B → A)
        → ((x : A) → g (f x) ≡ x)
        → ((y : B) → f (g y) ≡ y)
        → IsEquiv f
  isEquiv {f = f} g linv rinv =  λ where
    .inv → g
    .left-inverse  → linv
    .right-inverse y →
      f (g y)         ≡⟨ sym (rinv (f (g y))) ⟩
      f (g (f (g y))) ≡⟨ cong f (linv (g y))  ⟩
      f (g y)         ≡⟨ rinv y               ⟩
      y               ∎
    .left-right _  → UIP -- TODO: avoid UIP

  equiv : (f : A → B) (g : B → A)
        → ((x : A) → g (f x) ≡ x)
        → ((y : B) → f (g y) ≡ y)
        → A ≃ B
  equiv f g linv rinv .proj₁ = f
  equiv f g linv rinv .proj₂ = isEquiv g linv rinv

open Equivalence public using (IsEquiv; _≃_)

module List where
  open import Data.List.Base public using (List; []; _∷_; _++_) hiding (module List)
  open import Data.List.Relation.Unary.All  public using (All; []; _∷_) hiding (module All)
  open import Data.List.Relation.Unary.Any public using (Any; here; there) hiding (module Any)
  open import Data.List.Membership.Propositional public using (_∈_)

  variable
    @0 xs ys zs : List A

  lookup : All P xs → x ∈ xs → P x
  lookup (p ∷ _ ) (here refl) = p
  lookup (_ ∷ ps) (there i)   = lookup ps i

  module All = Data.List.Relation.Unary.All
  module Any = Data.List.Relation.Unary.Any

open List public using (List; []; _∷_; _++_; xs; ys; zs)

open import Data.Nat public using (ℕ; zero; suc)
module Nat = Data.Nat

module Maybe where
  open import Agda.Builtin.Maybe public using (Maybe; nothing; just) hiding (module Maybe)

  map : (A → B) → Maybe A → Maybe B
  map f nothing = nothing
  map f (just x) = just (f x)

open Maybe public using (Maybe; nothing; just)

module Sum where
  open import Data.Sum.Base public using (_⊎_; inj₁; inj₂)

  either : (@0 C : A ⊎ B → Set ℓ) →
           ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
           ((x : A ⊎ B) → C x)
  either C f g (inj₁ x) = f x
  either C f g (inj₂ y) = g y

  [_,_] : (A → C) → (B → C) → (A ⊎ B → C)
  [_,_] = either _

  map : (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
  map {A = A} {C = C} {B = B} {D = D} f g = [ (λ x → inj₁ (f x)) , (λ y → inj₂ (g y)) ]

  map₁ : (A → C) → (A ⊎ B → C ⊎ B)
  map₁ f = map f id

  map₂ : (B → D) → (A ⊎ B → A ⊎ D)
  map₂ = map id

  swap : A ⊎ B → B ⊎ A
  swap = [ (λ x → inj₂ x) , (λ y → inj₁ y) ]

open Sum public using (_⊎_; inj₁; inj₂; either)

module Dec where
  open import Relation.Nullary public using (Dec; yes; no) hiding (module Dec)
  open import Relation.Nullary.Decidable public

  ,-injective : {B : A → Set ℓ} {y₁ : B x₁} {y₂ : B x₂} 
              → _≡_ {A = Σ A B} (x₁ , y₁) (x₂ , y₂) 
              → Σ (x₁ ≡ x₂) λ x= → PathOver B x= y₁ y₂
  ,-injective refl = refl , refl

open Dec public using (Dec; yes; no)

it : {{A}} → A
it {{x}} = x

infix 0 case_of_

case_of_ : A → (A → B) → B
case x of f = f x
{-# INLINE case_of_ #-}


module Erased where

  record Erase (@0 A : Set a) : Set a where
    constructor erase
    field
      @0 get : A
  open Erase public
  
  Σ0 : (A : Set a) (B : @0 A → Set b) → Set (a ⊔ b)
  Σ0 A B = Σ (Erase A) (λ x → B (get x))

  pattern <_> x = _ , x

  -- Resurrection of erased values
  @0 Rezz : {@0 A : Set ℓ} (@0 x : A) → Set ℓ
  Rezz {A = A} x = Σ A (_≡ x)

  pattern rezz x = x , refl

  rezz-cong : (f : A → B) → Rezz x → Rezz (f x)
  rezz-cong f (rezz x) = rezz (f x)

  rezz-cong₂ : (f : A → B → C) → Rezz x → Rezz y → Rezz (f x y)
  rezz-cong₂ f (rezz x) (rezz y) = rezz (f x y)

open Erased public using (Erase; erase; get; Σ0; <_>; Rezz; rezz; rezz-cong; rezz-cong₂)
