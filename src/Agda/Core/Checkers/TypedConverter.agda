open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Rules.TypedConversion
open import Agda.Core.Reduce
open import Agda.Core.TCM.Instances
open import Agda.Core.Checkers.ConverterUtils


module Agda.Core.Checkers.TypedConverter
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



convertCheck : {{fl : Fuel}} → (Γ : Context α)  → (t q : Term α) → TCM (Γ ⊢ t ≅ q)


convertTermSs : {{fl : Fuel}} → (Γ : Context α) →
                (s p : TermS α rβ)
              → TCM (Γ ⊢ s ⇔ p)

convertTermSs ctx ⌈⌉ _ = return {!!}
convertTermSs r (x ↦ u ◂ s0) t = {!!}


convertCheck ⦃ None ⦄ _ _ _ =
  tcError "not enough fuel to check conversion"
convertCheck ⦃ More ⦄ ctx t q = do
  let 
    r = singScope ctx 
  t ⟨ tred ⟩ ← reduceTo r t
  q ⟨ qred ⟩ ← reduceTo r q
  {!!}

{-# COMPILE AGDA2HS convertTermSs #-}



