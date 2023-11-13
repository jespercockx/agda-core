{-# LANGUAGE ScopedTypeVariables #-}
module Reduce where

import Scope.Core (Scope)
import Scope.In (In, decIn)
import qualified Syntax (Branch(BBranch), Elim(EArg, ECase, EProj), Sort(STyp), Subst(SCons, SNil), Term(TApp, TCon, TDef, TLam, TLet, TPi, TSort, TVar), idEnv, liftBindEnv, liftEnv, lookupEnv, raiseEnv)

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

lookupBranch ::
             forall name defs cons conArity .
               Branches defs cons conArity ->
                 In -> Maybe (Term defs cons conArity)
lookupBranch [] k = Nothing
lookupBranch (Syntax.BBranch k' aty u : bs) p
  = case decIn k' p of
        True -> Just u
        False -> lookupBranch bs p

step ::
     forall name defs cons conArity .
       Scope -> Term defs cons conArity -> Maybe (Term defs cons conArity)
step (Syntax.TVar _) = Nothing
step (Syntax.TDef _) = Nothing
step (Syntax.TCon _ vs) = Nothing
step (Syntax.TLam u) = Nothing
step (Syntax.TApp u []) = step u
step (Syntax.TApp (Syntax.TLam u) (Syntax.EArg v : es))
  = Just (substTop α v u)
step (Syntax.TApp (Syntax.TCon k us) (Syntax.ECase bs : es))
  = case lookupBranch bs k of
        Just v -> Just (substTerm (Syntax.raiseEnv α us) v)
        Nothing -> Nothing
step (Syntax.TApp u es) = fmap (\ u -> TApp u es) (step u)
step (Syntax.TPi a b) = Nothing
step (Syntax.TSort x) = Nothing
step (Syntax.TLet u v)
  = case step u of
        Just u' -> Just (TLet u' v)
        Nothing -> Just (substTop α u v)

