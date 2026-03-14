open import Agda.Builtin.Equality

data Ctx : Set where
  •  : Ctx
  _▷ : Ctx → Ctx

variable
  Γ Δ Θ : Ctx

data Var : Ctx → Set where
  vz : Var (Γ ▷)
  vs : Var Γ → Var (Γ ▷)

data Tm (Γ : Ctx) : Set where
  var : Var Γ → Tm Γ
  app : Tm Γ → Tm Γ → Tm Γ
  lam : Tm (Γ ▷) → Tm Γ

Tms' : Ctx → Ctx → Set

record Tms (Δ Γ : Ctx) : Set where
  constructor tms
  inductive
  eta-equality
  field
    tms' : Tms' Δ Γ

record Tms• (Δ : Ctx) : Set where
  constructor ε'
  eta-equality

record Tms▷ (Δ : Ctx) (Γ : Ctx) : Set where
  constructor _,'_
  inductive
  eta-equality
  field
    π₁' : Tms Δ Γ
    π₂' : Tm Δ

Tms' Δ •     = Tms• Δ
Tms' Δ (Γ ▷) = Tms▷ Δ Γ

pattern _,_ δ t = tms (δ ,' t)
pattern ε       = tms ε'

-- Substitution (can define by induction on terms)
postulate
  _[_] : Tm Γ → Tms Δ Γ → Tm Δ

variable
  t u : Tm _
  δ σ : Tms _ _

test1 : ε ≡ δ
test1 = refl

test2 : ∀ {t : Tm •} → t [ δ ] ≡ t [ σ ]
test2 = refl

-- Context concatenation
_▷▷_ : Ctx → Ctx → Ctx
Γ ▷▷ •     = Γ
Γ ▷▷ (Δ ▷) = (Γ ▷▷ Δ) ▷

-- Vertical composition of substitutions
_◆_ : Tms Θ Γ → Tms Θ Δ → Tms Θ (Γ ▷▷ Δ)
_◆_ {Δ = •}   δ ε       = δ
_◆_ {Δ = Δ ▷} δ (σ , t) = (δ ◆ σ) , t

test3 : ∀ {σ : Tms Θ •} → δ ◆ σ ≡ δ
test3 = refl