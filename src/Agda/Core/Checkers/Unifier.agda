open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Syntax.Strengthening
open import Agda.Core.Syntax.VarInTerm
open import Agda.Core.TCM.Instances
open import Agda.Core.Rules.Unification
open UnificationStepAndStop
open TelescopeEq

module Agda.Core.Checkers.Unifier
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

renamingExtend : ∀ {@0 α β : Scope Name} {@0 x : Name} → Renaming α β → x ∈ β → Renaming  (α ▸ x) β
renamingExtend σ xInβ = λ zInx◃α → inBindCase zInx◃α σ (λ where refl → xInβ)

opaque
  unfolding Scope
  renamingWeaken : ∀ {@0 α β γ : Scope Name} → Singleton γ → Renaming α β → Renaming α (β <> γ)
  renamingWeaken (sing []) σ = σ
  renamingWeaken (sing (_ ∷ α)) σ = inThere ∘ (renamingWeaken (sing α) σ)

renamingWeakenVar : ∀ {@0 α β : Scope Name} {@0 x : Name} → Renaming α β → Renaming α  (β ▸ x)
renamingWeakenVar σ = inThere ∘ σ

opaque
  unfolding Scope
  renamingToSubst : ∀ {@0 α β : Scope Name} → Singleton α → Renaming α β → α ⇒ β
  renamingToSubst (sing []) _ = ⌈⌉
  renamingToSubst (sing (Erased x ∷ α)) r =
    let r' : Renaming α _
        r' = λ xp → r (coerce (subBindDrop subRefl) xp) in
    renamingToSubst (sing α) r' ▹ x ↦  TVar < r (Zero ⟨ IsZero refl ⟩) >



---------------------------------------------------------------------------------------------------
                             {- PART ONE : Context reordering -}
---------------------------------------------------------------------------------------------------

module Swap where
  private variable
    @0 x y : Name
    @0 α : Scope Name

  data SwapError : Set where
    CantSwapVarWithItSelf : SwapError
    VarInWrongOrder : SwapError

  opaque
    unfolding Scope
    swapTwoLast : Context (α ▸ x ▸ y) → Maybe (Context (α ▸ y ▸ x))
    swapTwoLast (CtxExtend (CtxExtend Γ y ay) x ax) = do
      ax' ← strengthen (subBindDrop subRefl) ax
      let ay' = weaken (subBindDrop subRefl) ay
      return ((Γ , x ∶ ax' ) , y ∶ ay')


    {- Idea of swapHighest (x, z, Γ) y:
        - terminaison condition : you swap x and y or fail
        - case 1: if you can swap the two first vars of (x, z, Γ) then
          do it and let Γ1Aux be the result of a recursive call on (x, Γ)
          return (z, Γ1Aux)
        - case 2: if case 1 fails then let Γ' be the result of the
          recursive call on (z, Γ) and return swapHighest (x, Γ') y
      (recursion terminates because the depth of y in the contexts
      used in recursive calls is decreasing.) -}
    swapHighest : {{fl : Index}} → Context  (α ▸ x) → ((⟨ y ⟩ yp) : NameIn α)
      → Maybe (Σ0 _ λ α' → Context α' × Renaming  (α ▸ x) α')
    swapHighest (CtxExtend (CtxExtend Γ0 y ay) x ax) (⟨ y ⟩ (Zero ⟨ IsZero refl ⟩)) = do
      Γ' ← swapTwoLast (CtxExtend (CtxExtend Γ0 y ay) x ax)
      let σ : Renaming (α ▸ y ▸ x) (α ▸ x ▸ y)
          σ = renamingExtend (renamingExtend (renamingWeaken (sing (_ ∷ _ ∷ [])) id) inHere) (inThere inHere)
      return < Γ' , σ >
    swapHighest {α = Erased z ∷ α}  {x = x} {{Suc fl}} (CtxExtend (CtxExtend Γ0 z az) x ax) (⟨ y ⟩ (Suc value ⟨ IsSuc proof ⟩)) =
      let Γ : Context (α ▸ z ▸ x)
          Γ = (CtxExtend (CtxExtend Γ0 z az) x ax)
          yInα : y ∈ α
          yInα = value ⟨ proof ⟩ in
      let areTheTwoLastVarsSwapable = do
        (CtxExtend Γ₁ .z az') ← swapTwoLast Γ
        ⟨ α₀' ⟩ (Γ₀' , σ₀ ) ← swapHighest {{fl}} Γ₁  < yInα >
        -- σ₀ : Renaming  (α ▸ x) α₀'
        let σ : Renaming (α ▸ z ▸ x) (α₀' ▸ z)
            σ = renamingExtend (renamingExtend ((renamingWeakenVar σ₀) ∘ inThere) inHere) (inThere (σ₀ inHere))
            az' : Type α₀'
            az' = subst (renamingToSubst (singScope Γ₁) σ₀) (weaken (subBindDrop subRefl) az)
            res1 : Σ0 _ λ α' → Context α' × Renaming (α ▸ z ▸ x) α'
            res1 = < CtxExtend Γ₀' z az' , σ >
        return res1 in
      let otherCase = do
        ⟨ γ₀ ⟩ (Δ₀ , τ₀) ← swapHighest {{fl}} (CtxExtend Γ0 z az) < yInα >
        -- τ₀ : Renaming (z ◃ α) γ₀
        let ax' : Type γ₀
            ax' = subst (renamingToSubst (singScope (CtxExtend Γ0 z az)) τ₀) ax
            σ₁ : Renaming (α ▸ z ▸ x) (γ₀ ▸ x)
            σ₁ = renamingExtend (renamingWeakenVar τ₀) inHere
        ⟨ α' ⟩ (Γ' , σ₂) ← swapHighest {{fl}} (CtxExtend Δ₀ x ax') < τ₀ (inThere yInα) >
        -- σ₂ : Renaming (x ◃ α₀') α'
        let res2 : Σ0 _ λ α' → Context α' × Renaming (α ▸ z ▸ x) α'
            res2 = < Γ' , σ₂ ∘ σ₁ >
        return res2 in
      caseMaybe areTheTwoLastVarsSwapable (λ x → Just x) otherCase
    swapHighest {{Zero}} (CtxExtend (CtxExtend _ _ _) _ _) (⟨ _ ⟩ (Suc _ ⟨ _ ⟩))  = Nothing -- this shouldn't happen as at all times fl ≥ position of y in the scope

    swap : Context α → (x y : NameIn α) → Either SwapError (Maybe (Σ0 _ λ α' → Context α' × Renaming α α'))
    swap _ Vzero Vzero = Left CantSwapVarWithItSelf
    swap Γ Vzero (Vsuc value proof) = do
      Right (swapHighest {{value}} Γ < (value ⟨ proof ⟩) >)
    swap _ (Vsuc _ _) Vzero = Left VarInWrongOrder
    swap _ Vone Vone = Left CantSwapVarWithItSelf
    swap _ (V2suc _ _) Vone = Left VarInWrongOrder
    swap (CtxExtend Γ z az) (Vsuc vx px) (V2suc vy py) = do
      Just (⟨ α₀' ⟩ (Γ0' , σ₀)) ← swap Γ (⟨ _ ⟩ (vx ⟨ px ⟩)) (⟨ _ ⟩ ((Suc vy) ⟨ IsSuc py ⟩))
        where Nothing → Right Nothing
      -- σ₀ : Renaming _ α₀'
      let τ₀ = renamingToSubst (singScope Γ) σ₀
          σ : Renaming (_ ▸ z) (α₀' ▸ z)
          σ = renamingExtend (renamingWeakenVar σ₀) inHere
      Right (Just < CtxExtend Γ0' z (subst τ₀ az), σ >)
  {-
  swapVarListFuel2 : Context α → (x : NameIn α) → (l : List (NameIn α)) → (fl : Nat) → @0 {{lengthNat l ≡ fl}} → Maybe (Σ0 _ λ α' → Context α' × Renaming α α')
  swapVarListFuel2 Γ (⟨ x ⟩ xp) ((⟨ y ⟩ yp) ∷ l) (suc fl) {{e}} = {!   !} --  do
    -- ⟨ _ ⟩ (Γ0' , σ₀) ← try_swap Γ (⟨ x ⟩ xp) (⟨ y ⟩ yp)
    -- let e : lengthNat (map (λ z → < σ₀ (proj₂ z) >) l) ≡ fl
    --     e = lengthMap ((λ z → < σ₀ (proj₂ z) >)) l
    -- ⟨ _ ⟩ (Γ' , σ) ← swapVarListFuel2 fl Γ0' (⟨ x ⟩ σ₀ xp) (map (λ z → < σ₀ (proj₂ z) >) l) {{e}}
    -- return < Γ' , σ ∘ σ₀ >
    -- where try_swap : Context α → (x y : NameIn α) → Maybe (Σ0 _ λ α' → Context α' × Renaming α α')
    --       try_swap Γ x y with (swap Γ x y)
    --       ... | Left CantSwapVarWithItSelf = Nothing
    --       ... | Left VarInWrongOrder = Just < Γ , id >
    --       ... | Right val = val
  swapVarListFuel2 Γ x [] zero = Just < Γ , id > -}

  swapVarListFuel : (fl : Nat) → Context α → (x : NameIn α) → (l : List (NameIn α)) → Maybe (Σ0 _ λ α' → Context α' × Renaming α α')
  swapVarListFuel (suc fl) Γ (⟨ x ⟩ xp) ((⟨ y ⟩ yp) ∷ l) = do
    ⟨ _ ⟩ (Γ0' , σ₀) ← try_swap Γ (⟨ x ⟩ xp) (⟨ y ⟩ yp)
    ⟨ _ ⟩ (Γ' , σ) ← swapVarListFuel fl Γ0' (⟨ x ⟩ σ₀ xp) (map (λ z → < σ₀ (proj₂ z) >) l)
    return < Γ' , σ ∘ σ₀ >
    where try_swap : Context α → (x y : NameIn α) → Maybe (Σ0 _ λ α' → Context α' × Renaming α α')
          try_swap Γ x y with (swap Γ x y)
          ... | Left CantSwapVarWithItSelf = Nothing
          ... | Left VarInWrongOrder = Just < Γ , id >
          ... | Right val = val
  swapVarListFuel zero Γ x [] = Just < Γ , id >
  swapVarListFuel _ _ _ _ = Nothing

  swapVarList : Context α → (x : NameIn α) → List (NameIn α) → Maybe (Σ0 _ λ α' → Context α' × Renaming α α')
  swapVarList Γ x l = swapVarListFuel (lengthNat l) Γ x l

  swapVarTerm : (Γ : Context α) → ((⟨ x ⟩ xp) : NameIn α) → (u : Term α)
    → Maybe (Σ0 _ λ α' → Context α' × Renaming α α')
  swapVarTerm Γ x u = swapVarList Γ x (varInTerm u)

  opaque
    swapVarTermStrengthened : (Γ : Context α) → ((⟨ x ⟩ xp) : NameIn α) → (u : Term α)
      → Maybe (Σ0 _ λ α' → Context α' × (Σ[ σ ∈ Renaming α α' ]
        (Σ[ u₀ ∈ Term (cutDrop (σ xp)) ] Strengthened (subst (renamingToSubst (singScope Γ) σ) u) u₀)))
    swapVarTermStrengthened Γ (⟨ x ⟩ xp) u =
      caseMaybe (swapVarTerm Γ (⟨ x ⟩ xp) u)
        (λ (⟨ α' ⟩ (Γ' , σ)) →
          let u' : Term α'
              u' = subst (renamingToSubst (singScope Γ) σ) u in
          caseMaybe (strengthen subCutDrop u')
            (λ u₀ {{e}} → Just (⟨ α' ⟩ (Γ' , (σ , (u₀ , (subCutDrop ⟨ e ⟩))))))
            Nothing)
        Nothing

{- End of module Swap -}
open Swap

---------------------------------------------------------------------------------------------------
                           {- PART TWO : Unification algorithm -}
---------------------------------------------------------------------------------------------------
{-
private variable
  @0 α β : Scope Name
  @0 x : Name
  Γ : Context α
  Ξ : TelescopicEq α β

data UnificationFailure (Γ : Context α) (Ξ : TelescopicEq α β) : Set where
  Stop : UnificationStops Γ Ξ → UnificationFailure Γ Ξ
  Error : String → UnificationFailure Γ Ξ
  Crash : String → UnificationFailure Γ Ξ

UnificationResult : (Γ : Context α) (Ξ : TelescopicEq α β) → Set
UnificationResult Γ Ξ = Either
    (UnificationFailure Γ Ξ)
    (Σ0[ γ ∈ Scope Name ] ∃[ Γ' ∈ Context γ ] UnificationSteps Γ Ξ Γ' (⌈⌉ ≟ ⌈⌉ ∶ ⌈⌉))

record UnificationValidStep (Γ : Context α) (Ξ : TelescopicEq α β) : Set where
  constructor UStep
  field
    @0 α' : Scope Name
    @0 β' : Scope Name
    Γ' : Context α'
    Ξ' : TelescopicEq α' β'
    step : UnificationStep Γ Ξ Γ' Ξ'

UnificationStepResult : (Γ : Context α) (Ξ : TelescopicEq α β) → Set
UnificationStepResult Γ Ξ = Either (UnificationFailure Γ Ξ) (UnificationValidStep Γ Ξ)

opaque
  unfolding Scope
  unifDeletion : (Γ : Context α) (Ξ : TelescopicEq α β) → UnificationStepResult Γ Ξ
  unifDeletion Γ (⌈ e ↦ aₗ ◃ σₗ ⌉ ≟ ⌈ e ↦ aᵣ ◃ σᵣ ⌉ ∶ ⌈ e ∶ t ◃ Δ ⌉) = {!   !}
  unifDeletion _ _ = Left (Error "deletion step not valid")

  unifSolution : (Γ : Context α) (Ξ : TelescopicEq α β) → UnificationStepResult Γ Ξ
  unifSolution Γ (⌈ e ↦ TVar x ◃ σₗ ⌉ ≟ ⌈ e ↦ TVar y ◃ σᵣ ⌉ ∶ ⌈ e ∶ t ◃ Δ ⌉) with compare x y
  ... | GT =
    let @0 α' : Scope Name
        α' = cutTake (proj₂ x) <> cutDrop (proj₂ x)
        yInα' : Maybe (_ ∈ α')
        yInα' = do {!   !} in
    caseMaybe yInα' {!   !} (Left (Crash "should be impossible"))

--    in Right (UStep _ _ {!   !} {!   !} {!   !})
  ... | EQ = Left (Error "solution step not valid")
  ... | LT = Right (UStep _ _ {!   !} {!   !} {!   !})
  unifSolution Γ (⌈ e ↦ TVar x ◃ σₗ ⌉ ≟ ⌈ e ↦ aᵣ ◃ σᵣ ⌉ ∶ ⌈ e ∶ t ◃ Δ ⌉) with (swapVarTerm Γ x aᵣ)
  ... | Nothing = Left (Error "check for CycleL")
  ... | Just (⟨ α' ⟩ (Γ' , aaa)) = {! s  !}
  unifSolution Γ (⌈ e ↦ αᵣ ◃ σₗ ⌉ ≟ ⌈ e ↦ TVar y ◃ σᵣ ⌉ ∶ ⌈ e ∶ t ◃ Δ ⌉) = {!   !}
  unifSolution _ _ = Left (Error "solution step not valid")


opaque
  unfolding Scope
  unification : (Γ : Context α) → (Ξ : TelescopicEq α β) → UnificationResult Γ Ξ
  unification Γ (⌈⌉ ≟ ⌈⌉ ∶ ⌈⌉) = Right < Γ ⟨ StepId Γ _ ⟩ >
  unification Γ (⌈ x ↦ aₗ ◃ σₗ ⌉ ≟ ⌈ x ↦ aᵣ ◃ σᵣ ⌉ ∶ ⌈ x ∶ t ◃ Δ ⌉) = {!   !}
-- -}
