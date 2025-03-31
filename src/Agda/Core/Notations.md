Notations used in Agda Core (updated on 31/03/2025)

---------------------------------------------------------------------------------------------------
symbols     input via agda          latex
⊢           |-                      \vdash
ˢ           ^s                      ^s
∶           :                       \vdotdot
▹           tw→                      \smalltriangleright
⇒           =>                      \Rightarrow
⌈           cuL                     \lceil
⌉           cuR                     \rceil
↦           r-|                     \mapsto
≟           ?=
↣           r->                     \rightarrowtail
ᵤ           _u                      _u
---------------------------------------------------------------------------------------------------

For Scopes : see notation file in Scope librairy

For context :
Γ , x ∶ t               CtxExtend Γ x t         extension of context Γ where x is of type t (a type)

For TermS Telescope and Substitution :
⌈⌉                      TSNil/EmptyTel/SNil     empty TermS/Telescope/Substitution
α ⇒ β                   Subst α β               substitution from α to β
x ↦ u ◂ ts              TSCons x u ts           extension of TermS ts where x is of associated to the term u (a term)
x ∶ t ◂ Δ               ExtendTel x t Δ         extension of telescope Δ where x is of type t (a type)
δ₁ ≟ δ₂ ∶ Δ             TelEq δ₁ δ₂ Δ           telescopic equality between the scopes δ₁ = δ₂ of type Δ
σ ▹ x ↦ u               SCons {x = x} σ u       extension of substitution σ where x is changed to u (a term)

For types :
Γ ⊢ u ∶ t               TyTerm Γ u t            In context Γ, u (a term) is of type t (a type)
Γ ⊢ˢ δ ∶ Δ              TySubst Γ δ Δ           In context Γ,  δ (a TemrS) is of type Δ (a Telescope)

Unification :
Γ , ΔEq ↣ᵤ Γ' , ΔEq'   UnificationStep Γ ΔEq Γ' ΔEq'
