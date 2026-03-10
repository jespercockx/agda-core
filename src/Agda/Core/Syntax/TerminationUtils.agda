open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.Rules.Conversion
open import Agda.Core.Rules.Typing

module Agda.Core.Syntax.TerminationUtils
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x      : Name
  @0 α      : Scope Name
  @0 dα      : Scope (NameIn defScope)
  @0 rβ     : RScope Name
  @0 u v    : Term α
  @0 a b c  : Type α
  @0 k l    : Sort α

data SubTermEnv : @0 Scope Name → Set where
  StEnvEmpty  : SubTermEnv mempty
  StEnvExtend : (@0 x : Name)
              → Maybe (NameIn α)   -- x is a sub-term of this variable (if any)
              → SubTermEnv α
              → SubTermEnv (α ▸ x)
{-# COMPILE AGDA2HS SubTermEnv #-}

-- data SubTermEnv (@0 otherScope : Scope Name) : @0 Scope Name → Set
-- data SubTermEnv otherScope where
--   StEnvEmpty  : SubTermEnv otherScope mempty
--   StEnvExtend : (@0 x : Name)
--               → Maybe (NameIn otherScope)   -- x is a sub-term of this variable (if any)
--               → SubTermEnv otherScope α
--               → SubTermEnv otherScope (α ▸ x)
-- {-# COMPILE AGDA2HS SubTermEnv #-}

private -- it should use a RScope instead of β and then could be public
  raiseNameIn : {@0 α β : Scope Name} → Singleton β → NameIn α →  NameIn (α <> β)
  raiseNameIn r n = weakenNameIn (subJoinDrop r subRefl) n
  {-# COMPILE AGDA2HS raiseNameIn #-}

opaque
  unfolding RScope extScope
  updateEnv : SubTermEnv α → (cs : RScope Name) → NameIn α → SubTermEnv (extScope α cs)
  updateEnv env [] _ = env
  updateEnv env (Erased x ∷ s) name = updateEnv (StEnvExtend x (Just name) env) s (weakenNameIn (subWeaken subRefl) name)
  {-# COMPILE AGDA2HS updateEnv #-}

lookupSt : (Γ : SubTermEnv α) (x : NameIn α) → Maybe (NameIn α)
lookupSt StEnvEmpty x = nameInEmptyCase x
lookupSt (StEnvExtend namesubterm nameparent c) name = 
  case (nameInBindCase name
    (λ q → lookupSt c (⟨ _ ⟩ q))
    (λ _ → nameparent)) of λ where
      (Just n) → Just (raiseNameIn (sing _) n)
      Nothing → Nothing
{-# COMPILE AGDA2HS lookupSt #-}

opaque
  unfolding Scope
  creatStEnvFromScope : SubTermEnv α → (β : Scope Name)  → SubTermEnv (α <> β)
  creatStEnvFromScope env [] = env
  creatStEnvFromScope env (Erased x ∷ rest) = StEnvExtend x Nothing (creatStEnvFromScope env rest)
{-# COMPILE AGDA2HS creatStEnvFromScope #-}

-- datatype for arbitrary member of a scope
data NthArg : @0 Scope Name → Set where
  ZeroNA : (@0 x : Name) → NthArg (α ▸ x)
  SucNA : (@0 x : Name) → NthArg α → NthArg (α ▸ x)
{-# COMPILE AGDA2HS NthArg deriving Show #-}

instance
  {-# NON_TERMINATING #-} -- need to find a way to not need those
  showNthArg : Show (NthArg α)
  showNthArg .show (ZeroNA x)  = "ZeroNA"
  showNthArg .show (SucNA x n) = "SucNA (" ++ show n ++ ")"
  showNthArg .showsPrec _ x s  = show x ++ s
  showNthArg .showList xs s    = show xs ++ s
-- {-# COMPILE AGDA2HS showNthArg #-}

-- indexOf : NthArg α → Index
-- indexOf (ZeroNA _) = Zero
-- indexOf (SucNA _ n) = Suc (indexOf n)
-- {-# COMPILE AGDA2HS indexOf #-}
opaque
  unfolding Scope
  lengthScope : Scope Name → Index
  lengthScope [] = Zero
  lengthScope (_ ∷ tl) = Suc $ lengthScope tl
{-# COMPILE AGDA2HS lengthScope #-}

lengthN : {a : Set} → List a → Index
lengthN []       = Zero
lengthN (_ ∷ xs) = Suc (lengthN xs)
{-# COMPILE AGDA2HS lengthN #-}

indexOf : Index → NthArg α → Index
indexOf (Suc n) (ZeroNA _) = n
indexOf (Suc n) (SucNA _ nNa) = indexOf n nNa
indexOf Zero _ = Zero -- should never be reached
{-# COMPILE AGDA2HS indexOf #-}


-- opaque
--   unfolding Scope
--   countLeft : (α : Scope Name) → NameIn α → Nat
--   countLeft (Erased x ∷ tl) (⟨ name ⟩ prf) = if {!!} then lengthScope tl else countLeft tl (⟨ name ⟩ prf)

getNthArg : NthArg α → NameIn α
getNthArg (ZeroNA x) = ⟨ x ⟩  (Zero ⟨ IsZero refl ⟩)
getNthArg {α} (SucNA x next)  = weakenNameIn (subWeaken subRefl) (getNthArg next)
{-# COMPILE AGDA2HS getNthArg #-}

opaque
  unfolding Scope
  iterateNthArg : (α : Scope Name) → List (NthArg α)
  iterateNthArg [] = []
  iterateNthArg (Erased x ∷ tl) = ZeroNA x ∷ (map (SucNA x) (iterateNthArg tl))
{-# COMPILE AGDA2HS iterateNthArg #-}

record FunDefinition : Set where
  no-eta-equality
  field
    index : NameIn defScope
    arity : Scope Name 
    body : Term arity
open FunDefinition public
{-# COMPILE AGDA2HS FunDefinition deriving Show #-}


botErased : {a : Set} → @0 ⊥ → a
botErased ()

-- try the left action, if it fails run the right action with the error
catchEither : {a : Set} → Either String a → (String → Either String a) → Either String a
catchEither (Right x) _ = Right x
catchEither (Left e)  f = f e
{-# COMPILE AGDA2HS catchEither #-}

eqNatSound : ∀ {x y : Nat} → (x == y) ≡ True → x ≡ y
eqNatSound {zero} {zero} h = refl
eqNatSound {suc n} {suc m} h = cong suc (eqNatSound h)
eqNatSound {zero} {suc _} ()
eqNatSound {suc _} {zero} ()

eqNatSoundFalse : ∀ {x y : Nat} → (x == y) ≡ False → (x ≡ y → ⊥)
eqNatSoundFalse {zero}  {zero}  h _ = case h of λ ()
eqNatSoundFalse {suc n} {suc m} h refl = eqNatSoundFalse {n} {m} h refl
eqNatSoundFalse {zero}  {suc _} h ()
eqNatSoundFalse {suc _} {zero}  h ()

decNat : ∀ (x y : Nat) → Dec (x ≡ y)
decNat x y = case (x == y) of λ where
  True {{ eq }} → True ⟨ eqNatSound eq ⟩
  False {{ eq }} → False ⟨ eqNatSoundFalse eq ⟩
{-# COMPILE AGDA2HS decNat #-}

eqIndexSound : ∀ {x y : Index} → (x == y) ≡ True → x ≡ y
eqIndexSound {Zero}  {Zero}  h = refl
eqIndexSound {Suc n} {Suc m} h = cong Suc (eqIndexSound h)
eqIndexSound {Zero}  {Suc _} ()
eqIndexSound {Suc _} {Zero}  ()

eqIndexSoundFalse : ∀ {x y : Index} → (x == y) ≡ False → (x ≡ y → ⊥)
eqIndexSoundFalse {Zero}  {Zero}  h _ = case h of λ ()
eqIndexSoundFalse {Suc n} {Suc m} h refl = eqIndexSoundFalse {n} {m} h refl
eqIndexSoundFalse {Zero}  {Suc _} h ()
eqIndexSoundFalse {Suc _} {Zero}  h ()

decIndex : ∀ (x y : Index) → Dec (x ≡ y)
decIndex x y = case (x == y) of λ where
  True  {{ eq }} → True  ⟨ eqIndexSound eq ⟩
  False {{ eq }} → False ⟨ eqIndexSoundFalse eq ⟩
{-# COMPILE AGDA2HS decIndex #-}

decMaybeNameIn : ∀ (x y : Maybe (NameIn α)) → Dec (x ≡ y)
decMaybeNameIn (Just a) (Just b) = case decNamesIn a b of λ where
  (True  ⟨ p ⟩) → True  ⟨ cong Just p ⟩
  (False ⟨ f ⟩) → False ⟨ (λ where refl → botErased (f refl)) ⟩
decMaybeNameIn Nothing  Nothing  = True ⟨ refl ⟩
decMaybeNameIn (Just _) Nothing  = False ⟨ (λ ()) ⟩
decMaybeNameIn Nothing  (Just _) = False ⟨ (λ ()) ⟩
{-# COMPILE AGDA2HS decMaybeNameIn #-}

transSym : {x y : RScope Name} (p : x ≡ y) → (t : Term (α ◂▸ x)) → subst0 (λ (@0 f₁) → Term (α ◂▸ f₁)) (trans p (sym p)) t ≡ t
transSym refl _ = refl

