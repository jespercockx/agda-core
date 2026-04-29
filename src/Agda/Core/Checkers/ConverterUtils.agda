open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.TCM.Instances

module Agda.Core.Checkers.ConverterUtils
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where


-- Workaround for https://github.com/agda/agda2hs/issues/324
{-# FOREIGN AGDA2HS import Agda.Core.TCM.Instances #-}

private open module @0 G = Globals globals

private variable
  @0 x y : Name
  @0 α β : Scope Name
  @0 rβ : RScope Name


reduceTo : {@0 α : Scope Name} (r : Singleton α) (v : Term α)
         → TCM (∃[ t ∈ Term α ] (ReducesTo v t))
reduceTo r v = do
  (I {{fl}}) ← tcmFuel
  rsig ← tcmSignature
  case reduce r rsig v of λ where
    Nothing        → tcError "not enough fuel to reduce a term"
    (Just u) ⦃ p ⦄ → return $ u ⟨ ⟨ r ⟩ ⟨ rsig ⟩ it ⟨ p ⟩ ⟩
{-# COMPILE AGDA2HS reduceTo #-}

reduceToPi : {@0 α : Scope Name} (r : Singleton α)
           → (v : Term α)
           → String
           → TCM (Σ0[ x ∈ Name                        ]
                   ∃[ (a , b) ∈ Type α × Type  (α ▸ x) ]
                   ReducesTo v (TPi x a b))
reduceToPi r v err = reduceTo r v >>= λ where
  (TPi x a b ⟨ redv ⟩) → return (⟨ x ⟩ ((a , b) ⟨ redv ⟩))
  _ → tcError err
{-# COMPILE AGDA2HS reduceToPi #-}

reduceToData : {@0 α : Scope Name} (r : Singleton α)
           → (v : Term α)
           → String
           → TCM (Σ[ d ∈ NameIn dataScope ]
                  ∃[ (pars , ixs) ∈ (TermS α (dataParScope d)) × (TermS α (dataIxScope d)) ]
                  ReducesTo v (TData d pars ixs))
reduceToData r v err = reduceTo r v >>= λ where
  (TData d pars ixs ⟨ redv ⟩) → return (d , (pars , ixs) ⟨ redv ⟩)
  _ → tcError err
{-# COMPILE AGDA2HS reduceToData #-}

reduceToRec : {@0 α : Scope Name} (r : Singleton α)
          → (v : Term α)
          → String
          → TCM (Σ[ rn ∈ NameIn recScope ]
                 ∃[ pars ∈ TermS α (recParScope rn) ]
                 ReducesTo v (TRec rn pars))
reduceToRec r v err = reduceTo r v >>= λ where
  (TRec rn pars ⟨ redv ⟩) → return (rn , pars ⟨ redv ⟩)
  _ → tcError err
{-# COMPILE AGDA2HS reduceToRec #-}

reduceToTRecCon : {@0 α : Scope Name} (r : Singleton α)
          → (v : Term α)
          → String
          → TCM (Σ[ rn ∈ NameIn recScope ]
                 ∃[ args ∈ TermS α (recFieldScope rn)]
                 ReducesTo v (TRecCon rn args))
reduceToTRecCon r v err = reduceTo r v >>= λ where
  (TRecCon rn args ⟨ redv ⟩) → return (rn , (args ⟨ redv ⟩))
  _ → tcError err
{-# COMPILE AGDA2HS reduceToTRecCon #-}

reduceToSort : {@0 α : Scope Name} (r : Singleton α)
           → (v : Term α)
           → String
           → TCM (∃[ s ∈ Sort α ] ReducesTo v (TSort s))
reduceToSort r v err = reduceTo r v >>= λ where
  (TSort s ⟨ redv ⟩) → return (s ⟨ redv ⟩)
  _ → tcError err
{-# COMPILE AGDA2HS reduceToSort #-}
