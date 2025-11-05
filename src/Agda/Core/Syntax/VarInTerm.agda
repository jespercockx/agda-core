open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax.Term

module Agda.Core.Syntax.VarInTerm
  {{@0 globals : Globals}}
  where

private open module @0 G = Globals globals

private variable
  @0 x  : Name
  @0 α  : Scope Name
  @0 rγ : RScope Name
  @0 d  : NameData
  @0 c  : NameCon d
  @0 cs : RScope (NameCon d)

opaque
  unfolding Scope
  liftBindListNameIn : List (NameIn (α ▸ x)) → List (NameIn α)
  liftBindListNameIn [] = []
  liftBindListNameIn ((⟨ x ⟩ (Zero ⟨ p ⟩)) ∷ l) = liftBindListNameIn l
  liftBindListNameIn ((⟨ x ⟩ (Suc n ⟨ IsSuc p ⟩)) ∷ l) = < n ⟨ p ⟩ > ∷ (liftBindListNameIn l)

  liftListNameIn : Singleton rγ → List (NameIn (α ◂▸ rγ)) → List (NameIn α)
  liftListNameIn _ [] = []
  liftListNameIn {rγ = rγ} rγRun ((⟨ x ⟩ xInγα) ∷ l) =
    let @0 γ : Scope Name
        γ = [] ◂▸ rγ
        @0 e : α ◂▸ rγ ≡ γ ++ α
        e = extScopeConcatEmpty _ rγ
        γRun : Singleton γ
        γRun = singExtScope (sing []) rγRun in
          (inJoinCase γRun (subst0 (λ β → _ ∈ β) e xInγα)
              (λ xInα → < xInα > ∷ (liftListNameIn rγRun l))
              (λ _ → liftListNameIn rγRun l))

{- TODO: create merge function for sorted lists of var as replacing <> by it would **greatly** decrease complexity -}
varInTerm : Term α → List (NameIn α)
varInTermS : TermS α rγ → List (NameIn α)
varInType : Type α → List (NameIn α)
varInBranches : Branches α d cs → List (NameIn α)
varInBranch : Branch α {d = d} c → List (NameIn α)

varInTerm (TVar x) = x ∷ []
varInTerm (TDef d) = []
varInTerm (TData d ps is) = varInTermS is <> (varInTermS ps)
varInTerm (TCon c vs) = varInTermS vs
varInTerm (TLam x v) = liftBindListNameIn (varInTerm v)
varInTerm (TApp t₀ t₁) = varInTerm t₀ <> (varInTerm t₁)
varInTerm (TProj t x) = varInTerm t
varInTerm (TCase d r u bs m) =
  varInTerm u <>
  (varInBranches bs) <>
  (liftListNameIn r (liftBindListNameIn (varInType m)))
varInTerm (TPi x a b) = varInType a <> (liftBindListNameIn (varInType b))
varInTerm (TSort x) = []
varInTerm (TLet x t t₁) = varInTerm t <> (liftBindListNameIn (varInTerm t₁))
varInTerm (TAnn u t) = varInTerm u <> varInType t

varInTermS ⌈⌉ = []
varInTermS (x ↦ u ◂ σ) = (varInTerm u) <> (varInTermS σ)

varInType (El _ u) = varInTerm u

varInBranches BsNil = []
varInBranches (BsCons b bs) = varInBranch b <> (varInBranches bs)

varInBranch (BBranch rc r v) = liftListNameIn r (varInTerm v)
