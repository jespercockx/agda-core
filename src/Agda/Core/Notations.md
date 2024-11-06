Notations used in Agda Core (updated on 24/11/06)

---------------------------------------------------------------------------------------------------
symbols     input via agda          latex
≡           ==                      \equiv
⊢           |-                      \vdash
ˢ           ^s                      ^s
∶           :                       \vdotdot
◃           tw                      \smalltriangleleft
∈           in                      \in
⊆           sub=                    \subseteq
⋈           join                    \bowtie
⇒           =>                      \Rightarrow
⌈           cuL                     \lceil
⌉           cuR                     \rceil
↦           r-|                     \mapsto
≟           ?=                      
↣           r->                     \rightarrowtail
ᵤ           _u                      _u
---------------------------------------------------------------------------------------------------

For Scopes :
α <> β                  α <> β                  Concatenation of scope α at the end of scope β
~ α                     revScope α              scope α reversed
α ⊆ β                   Sub α β                 α is a sub-scope of β
[ x ]                   singleton x             Scope of one element x
x ∈ α                   In x α                  singleton x ⊆ α
x ◃ α                   bind x α                Adds element x to scope α
α ⋈ β ≡ γ               Split α β γ             scope γ is a mix of elements of α and β

For context
Γ , x ∶ t               CtxExtend Γ x t         extension of context Γ where x is of type t (a type)

For substitution and telescope :
α ⇒ β                   Subst α β               substitution from α to β
⌈⌉                      SNil/EmptyTel/EmptyEq   empty substitution/telescope/telescopic equality
⌈ x ↦ u ◃ σ ⌉           SCons {x = x} u σ       extension of substitution σ where x is changed to u (a term)
⌈ x ∶ t ◃ Δ ⌉           ExtendTel x t Δ         extension of telescope Δ where x is of type t (a type)
⌈ u ≟ v ∶ t ◃ ΔEq ⌉     ExtendEq u v t ΔEq      extension of telescopic equality ΔEq where u = v : t

For types :
Γ ⊢ u ∶ t               TyTerm Γ u t            In context Γ, u (a term) is of type t (a type)
Γ ⊢ˢ δ ∶ Δ              TySubst Γ δ Δ           In context Γ,  δ (a substitution) is of type Δ (a telescope)

Unification :
Γ , ΔEq ↣ᵤ Γ' , ΔEq'   UnificationStep Γ ΔEq Γ' ΔEq'
