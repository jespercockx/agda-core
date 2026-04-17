module Agda.Core.TestProjection where

open import Agda.Core.Prelude

open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.TCM.TCM
open import Agda.Core.Rules.Typing
open import Agda.Core.Checkers.TypeCheck
open import Agda.Core.Rules.Unification
open import Agda.Core.Checkers.Unifier

private variable
  x y : Name
  α : Scope Name

datas = mempty ▸ "Bool" ▸ "Nat" ▸ "Vector"
records = mempty ▸ "Σ"

instance
  globals : Globals
  globals = record
    { defScope = {!!}
    ; dataScope = datas
    ; recScope = records
    ; dataParScope = λ where
      --Vector
      (⟨ name ⟩ (Zero ⟨ proof₁ ⟩)) -> rsingleton "A"
      --Nat and Bool
      _ -> mempty
    ; dataIxScope = λ where
      --Vector
      (⟨ name ⟩ (Zero ⟨ proof₁ ⟩)) -> rsingleton "length"
      --Nat and Bool
      _ -> mempty
    ; dataConstructors = λ where
      --Vector
      (⟨ name ⟩ (Zero ⟨ proof₁ ⟩)) -> "Nil" ◂ "Cons" ◂ mempty
      --Nat 
      (⟨ name ⟩ (Suc Zero ⟨ proof₁ ⟩)) -> "Zero" ◂ "Suc" ◂ mempty
      -- and Bool
      _ -> "True" ◂ "False" ◂ mempty 
    ; dataFieldScope = λ where 
      -- True
      {d = ⟨ _ ⟩ (Suc (Suc Zero) ⟨ _ ⟩)} (⟨ _ ⟩ (Zero ⟨ _ ⟩)) → mempty
      -- False
      {d = ⟨ _ ⟩ (Suc (Suc Zero) ⟨ _ ⟩)} (⟨ _ ⟩ (Suc (Zero) ⟨ _ ⟩)) → mempty
      -- Zero
      {d = ⟨ _ ⟩ (Suc (Zero) ⟨ _ ⟩)} (⟨ _ ⟩ (Zero ⟨ _ ⟩)) → mempty
      -- Suc
      {d = ⟨ _ ⟩ (Suc (Zero) ⟨ _ ⟩)} (⟨ _ ⟩ (Suc (Zero) ⟨ _ ⟩)) → "base" ◂ mempty
      -- Nil
      {d = ⟨ _ ⟩ (Zero ⟨ _ ⟩)} (⟨ _ ⟩ (Zero ⟨ _ ⟩)) → {!   !}
      -- Cons
      _ → {!   !}
    ; recParScope = λ where 
      -- Σ
      _ → "a" ◂ "b" ◂ mempty
    ; recFieldScope = λ where 
      -- Σ
      _ → {!!}
    ; recCon = λ where 
      -- Σ
      _ → {!!}
    }
open module @0 G = Globals globals


opaque
  unfolding ScopeThings

  nameBool : NameData
  nameBool = ⟨ "Bool" ⟩ (Suc (Suc Zero) ⟨ IsSuc (IsSuc (IsZero refl)) ⟩)

  nameNat : NameData
  nameNat = ⟨ "Nat" ⟩ (Suc Zero ⟨ IsSuc (IsZero refl) ⟩)

  nameVector : NameData
  nameVector = ⟨ "Vector" ⟩ (Zero ⟨ IsZero refl ⟩)

  




-- sigDataInstance : (d : NameData) → Datatype d
-- --Vector
-- sigDataInstance (⟨ name ⟩ (Zero ⟨ proof₁ ⟩)) = 
--   record { dataSort = STyp 0 ; dataParTel = {!!} ; dataIxTel = {!!}; dataConstructors = []}
-- --Nat
-- sigDataInstance (⟨ name ⟩ ((Suc Zero) ⟨ proof₁ ⟩)) = 
--   record { dataSort = STyp 0 ; dataParTel = EmptyTel ; dataIxTel = EmptyTel; dataConstructors = []}
-- --Bool
-- sigDataInstance (⟨ name ⟩ (sucsuczero ⟨ proof₁ ⟩)) = record { dataSort = STyp 0 ; dataParTel = EmptyTel ; dataIxTel = EmptyTel; dataConstructors = []}



-- boolsigcons : {@0 d : NameData} (c : NameDataCon d) → DataConstructor {d = d} c
-- boolsigcons _  = record { conIndTel = EmptyTel; conIx = TSNil }


-- instance
--   sig : Signature
--   sig .sigData = λ where 
--               _ → record { dataSort = STyp 0 ; dataParTel = EmptyTel ; dataIxTel = EmptyTel; dataConstructors = []}
--   sig .sigDefs n = nameInEmptyCase n
--   sig .sigRecs rn = nameInEmptyCase rn
--   sig .sigCons d c = boolsigcons {d = d} c

instance
  {-# TERMINATING #-}
  fuel : Fuel
  fuel = More {{fuel}}

opaque
  unfolding ScopeThings nameBool nameNat nameVector

  nameTrue : NameDataCon nameBool
  nameTrue = ⟨ 'T' ∷ 'r' ∷ 'u' ∷ 'e' ∷ [] ⟩ (Zero ⟨ IsZeroR refl ⟩)

  nameFalse : NameDataCon nameBool
  nameFalse = ⟨ "False" ⟩ inRThere inRHere

  nameZero : NameDataCon nameNat
  nameZero = ⟨ "Zero" ⟩ inRHere

  nameSuc : NameDataCon nameNat
  nameSuc = ⟨ "Suc" ⟩ inRThere inRHere

  nameNil : NameDataCon nameVector
  nameNil = ⟨ "Nil" ⟩ inRHere

  nameCons : NameDataCon nameVector
  nameCons = ⟨ "Cons" ⟩ inRThere inRHere


module TestTypechecker (@0 x y z : Name) where

  opaque

    testTerm₁ : Term α
    testTerm₁ = TLam x (TVar (⟨ x ⟩ inHere))
