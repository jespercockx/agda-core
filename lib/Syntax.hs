module Syntax where

import Numeric.Natural (Natural)
import Scope (In)

data Term = TVar In
          | TDef In
          | TCon In
          | TLam Term
          | TApp Term Elims
          | TPi Term Term
          | TSort Sort
          | TLet Term Term

data Sort = STyp Natural

data Elim = EArg Term
          | EProj In
          | ECase Branches

data Elims = ESNil
           | ESCons Elim Elims

data Branch = BBranch In

data Branches = BNil
              | BCons Branch Branches

type Type = Term

data Subst = SNil
           | SCons Term Subst

