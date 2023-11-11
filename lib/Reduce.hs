{-# LANGUAGE ScopedTypeVariables #-}
module Reduce where

import Scope.Core (Scope)
import qualified Syntax (Branch(BBranch), Elim(EArg, ECase, EProj), Sort(STyp), Subst(SCons, SNil), Term(TApp, TCon, TDef, TLam, TLet, TPi, TSort, TVar), idEnv, liftBindEnv, liftEnv, lookupEnv)

substTerm ::
          forall name defs cons conArity .
            Subst defs cons conArity ->
              Term defs cons conArity -> Term defs cons conArity
substTerm f (Syntax.TVar k) = Syntax.lookupEnv f k
substTerm f (Syntax.TDef k) = TDef k
substTerm f (Syntax.TCon k vs) = TCon k (substEnv f vs)
substTerm f (Syntax.TLam v)
  = TLam (substTerm (Syntax.liftBindEnv f) v)
substTerm f (Syntax.TApp u es)
  = TApp (substTerm f u) (substElims f es)
substTerm f (Syntax.TPi a b)
  = TPi (substTerm f a) (substTerm (Syntax.liftBindEnv f) b)
substTerm f (Syntax.TSort s) = TSort (substSort f s)
substTerm f (Syntax.TLet u v)
  = TLet (substTerm f u) (substTerm (Syntax.liftBindEnv f) v)

substSort ::
          forall name defs cons conArity .
            Subst defs cons conArity ->
              Sort defs cons conArity -> Sort defs cons conArity
substSort f (Syntax.STyp x) = STyp x

substElim ::
          forall name defs cons conArity .
            Subst defs cons conArity ->
              Elim defs cons conArity -> Elim defs cons conArity
substElim f (Syntax.EArg u) = EArg (substTerm f u)
substElim f (Syntax.EProj k) = EProj k
substElim f (Syntax.ECase bs) = ECase (substBranches f bs)

substElims ::
           forall name defs cons conArity .
             Subst defs cons conArity ->
               Elims defs cons conArity -> Elims defs cons conArity
substElims f [] = []
substElims f (e : es) = substElim f e : substElims f es

substBranch ::
            forall name defs cons conArity .
              Subst defs cons conArity ->
                Branch defs cons conArity -> Branch defs cons conArity
substBranch f (Syntax.BBranch k aty u)
  = BBranch k aty (substTerm (Syntax.liftEnv aty f) u)

substBranches ::
              forall name defs cons conArity .
                Subst defs cons conArity ->
                  Branches defs cons conArity -> Branches defs cons conArity
substBranches f [] = []
substBranches f (b : bs) = substBranch f b : substBranches f bs

substEnv ::
         forall name defs cons conArity .
           Subst defs cons conArity ->
             Subst defs cons conArity -> Subst defs cons conArity
substEnv f Syntax.SNil = SNil
substEnv f (Syntax.SCons x e)
  = SCons (substTerm f x) (substEnv f e)

substTop ::
         forall name defs cons conArity .
           Scope ->
             Term defs cons conArity ->
               Term defs cons conArity -> Term defs cons conArity
substTop r u = substTerm (SCons u (Syntax.idEnv r))

