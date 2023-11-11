{-# LANGUAGE ScopedTypeVariables #-}
module Syntax where

import Numeric.Natural (Natural)
import Scope.Core (Scope, singleton)
import Scope.In (In, bindSubToIn, coerce, inBindCase, inEmptyCase, inHere)
import Scope.Split (splitRefl)
import Scope.Sub (Sub, joinSubRight, subBindDrop, subBindKeep, subJoinKeep, subRefl, subRight)

data Term = TVar In
          | TDef In
          | TCon In Subst
          | TLam Term
          | TApp Term Elims
          | TPi Term Term
          | TSort Sort
          | TLet Term Term

data Sort = STyp Natural

data Elim = EArg Term
          | EProj In
          | ECase Branches

data Branch = BBranch In Scope Term

type Elims = [Elim]

type Branches = [Branch]

type Type = Term

data Subst = SNil
           | SCons Term Subst

elimView :: forall name defs cons conArity . Term -> (Term, Elims)
elimView (TApp u es2)
  = case elimView u of
        (u', es1) -> (u', es1 ++ es2)
elimView u = (u, [])

lookupEnv :: forall name defs cons conArity . Subst -> In -> Term
lookupEnv SNil q = inEmptyCase
lookupEnv (SCons u f) q = inBindCase q u (lookupEnv f)

weaken :: forall name defs cons conArity . Sub -> Term -> Term
weaken p (TVar k) = TVar (coerce p k)
weaken p (TDef k) = TDef k
weaken p (TCon k vs) = TCon k (weakenEnv p vs)
weaken p (TLam v) = TLam (weaken (subBindKeep p) v)
weaken p (TApp u es) = TApp (weaken p u) (weakenElims p es)
weaken p (TPi a b) = TPi (weaken p a) (weaken (subBindKeep p) b)
weaken p (TSort α) = TSort (weakenSort p α)
weaken p (TLet v t) = TLet (weaken p v) (weaken (subBindKeep p) t)

weakenSort :: forall name defs cons conArity . Sub -> Sort -> Sort
weakenSort p (STyp x) = STyp x

weakenElim :: forall name defs cons conArity . Sub -> Elim -> Elim
weakenElim p (EArg x) = EArg (weaken p x)
weakenElim p (EProj k) = EProj k
weakenElim p (ECase bs) = ECase (weakenBranches p bs)

weakenElims ::
            forall name defs cons conArity . Sub -> Elims -> Elims
weakenElims p [] = []
weakenElims p (e : es) = weakenElim p e : weakenElims p es

weakenBranch ::
             forall name defs cons conArity . Sub -> Branch -> Branch
weakenBranch p (BBranch k r x)
  = BBranch k r (weaken (subJoinKeep r p) x)

weakenBranches ::
               forall name defs cons conArity . Sub -> Branches -> Branches
weakenBranches p [] = []
weakenBranches p (b : bs) = weakenBranch p b : weakenBranches p bs

weakenEnv :: forall name defs cons conArity . Sub -> Subst -> Subst
weakenEnv p SNil = SNil
weakenEnv p (SCons u e) = SCons (weaken p u) (weakenEnv p e)

idEnv :: forall name defs cons conArity . Scope -> Subst
idEnv [] = SNil
idEnv (x : β)
  = SCons (TVar inHere) (weakenEnv (subBindDrop subRefl) (idEnv β))

liftEnv :: forall name defs cons conArity . Scope -> Subst -> Subst
liftEnv [] e = e
liftEnv (x : α) e
  = SCons (TVar inHere)
      (weakenEnv (subBindDrop subRefl) (liftEnv α e))

liftBindEnv :: forall name defs cons conArity . Subst -> Subst
liftBindEnv e
  = SCons (TVar inHere) (weakenEnv (subBindDrop subRefl) e)

coerceEnv ::
          forall name defs cons conArity . Scope -> Sub -> Subst -> Subst
coerceEnv [] p e = SNil
coerceEnv (x : α) p e
  = SCons (lookupEnv e (bindSubToIn p))
      (coerceEnv α (joinSubRight singleton p) e)

dropEnv :: forall name defs cons conArity . Subst -> Subst
dropEnv (SCons x f) = f

raiseEnv ::
         forall name defs cons conArity . Scope -> Subst -> Subst
raiseEnv r SNil = idEnv r
raiseEnv r (SCons u e) = SCons u (raiseEnv r e)

raise :: forall name defs cons conArity . Scope -> Term -> Term
raise r = weaken (subRight (splitRefl r))

