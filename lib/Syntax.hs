{-# LANGUAGE ScopedTypeVariables #-}
module Syntax where

import Numeric.Natural (Natural)
import Scope (All, In, Scope, Sub, bindCase, coerce, emptyCase, lookupAll, subBindKeep, subJoinKeep)

type ConArities = All Scope

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

type Elims = [Elim]

data Branch = BBranch In Term

type Branches = [Branch]

type Type = Term

data Subst = SNil
           | SCons Term Subst

elimView :: forall name defs cons . Term -> (Term, Elims)
elimView (TApp u es2)
  = case elimView u of
        (u', es1) -> (u', es1 ++ es2)
elimView u = (u, [])

lookupEnv :: forall name defs cons . Subst -> In -> Term
lookupEnv SNil q = emptyCase
lookupEnv (SCons u f) q = bindCase q u (lookupEnv f)

weaken :: forall name defs cons . ConArities -> Sub -> Term -> Term
weaken ars p (TVar k) = TVar (coerce p k)
weaken ars p (TDef k) = TDef k
weaken ars p (TCon k vs) = TCon k (weakenEnv ars p vs)
weaken ars p (TLam v) = TLam (weaken ars (subBindKeep p) v)
weaken ars p (TApp u es)
  = TApp (weaken ars p u) (weakenElims ars p es)
weaken ars p (TPi a b)
  = TPi (weaken ars p a) (weaken ars (subBindKeep p) b)
weaken ars p (TSort α) = TSort (weakenSort ars p α)
weaken ars p (TLet v t)
  = TLet (weaken ars p v) (weaken ars (subBindKeep p) t)

weakenSort ::
           forall name defs cons . ConArities -> Sub -> Sort -> Sort
weakenSort ars p (STyp x) = STyp x

weakenElim ::
           forall name defs cons . ConArities -> Sub -> Elim -> Elim
weakenElim ars p (EArg x) = EArg (weaken ars p x)
weakenElim ars p (EProj k) = EProj k
weakenElim ars p (ECase bs) = ECase (weakenBranches ars p bs)

weakenElims ::
            forall name defs cons . ConArities -> Sub -> Elims -> Elims
weakenElims ars p [] = []
weakenElims ars p (e : es)
  = weakenElim ars p e : weakenElims ars p es

weakenBranch ::
             forall name defs cons . ConArities -> Sub -> Branch -> Branch
weakenBranch ars p (BBranch k x)
  = BBranch k (weaken ars (subJoinKeep (lookupAll ars k) p) x)

weakenBranches ::
               forall name defs cons . ConArities -> Sub -> Branches -> Branches
weakenBranches ars p [] = []
weakenBranches ars p (b : bs)
  = weakenBranch ars p b : weakenBranches ars p bs

weakenEnv ::
          forall name defs cons . ConArities -> Sub -> Subst -> Subst
weakenEnv ars p SNil = SNil
weakenEnv ars p (SCons u e)
  = SCons (weaken ars p u) (weakenEnv ars p e)

