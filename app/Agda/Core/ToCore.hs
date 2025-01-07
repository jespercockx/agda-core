{-# LANGUAGE TypeFamilies, OverloadedStrings #-}

-- | Conversion from Agda's internal syntax to core representation
module Agda.Core.ToCore
  ( ToCore(..)
  , ToCoreM
  , Defs
  , Cons
  , convert
  ) where

import Control.Monad (when)
import Control.Monad.Reader (ReaderT, runReaderT, MonadReader, asks)
import Control.Monad.Except (MonadError(throwError))
import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import Numeric.Natural (Natural)

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Internal (lensSort, unDom, unEl)
import Agda.Syntax.Internal.Elim (allApplyElims)
import Agda.Syntax.Common.Pretty
import Agda.TypeChecking.Substitute ()
import Agda.TypeChecking.Substitute.Class (Subst, absBody, raise)
import Agda.Utils.Maybe (fromMaybeM, whenNothingM)
import Agda.Utils.Lens ((^.))

import Data.Map.Strict      qualified as Map
import Agda.Syntax.Internal qualified as I

import Agda.Core.Syntax (Term(..), Sort(..))
import Agda.Core.Syntax qualified as Core

import Scope.In (Index)
import Scope.In qualified as Scope

-- | Global definitions are represented as a mapping from @QName@s
--   to proofs of global def scope membership.
type Defs = Map QName Index

-- | Same for constructors, for the global scope of all constructors.
type Cons = Map QName Index


-- TODO(flupe): move this to Agda.Core.Syntax
-- | Apply a core term to elims
tApp :: Term -> [Term] -> Term
tApp t []     = t
tApp t (e:es) = TApp t e `tApp` es

-- | Global information available during translation.
type ToCoreGlobal = (Defs, Cons)

-- | Custom monad used for translating to core syntax.
--   Gives access to global defs and constructors.
--   Translation may fail.
newtype ToCoreM a = ToCoreM { runToCore :: ReaderT ToCoreGlobal (Either Doc) a }
  deriving newtype (Functor, Applicative, Monad, MonadError Doc)
  deriving newtype (MonadReader ToCoreGlobal)

asksDef :: (Defs -> a) -> ToCoreM a
asksDef = asks . (. fst)

asksCons :: (Cons -> a) -> ToCoreM a
asksCons = asks . (. snd)

-- | Lookup a definition name in the current module.
--   Fails if the definition cannot be found.
lookupDef :: QName -> ToCoreM Index
lookupDef qn = fromMaybeM complain $ asksDef (Map.!? qn)
  where complain = throwError $ "Trying to access a definition from another module: " <+> pretty qn
        --
-- | Lookup a constructor name in the current module.
--   Fails if the constructor cannot be found.
lookupCons :: QName -> ToCoreM Index
lookupCons qn = fromMaybeM complain $ asksCons (Map.!? qn)
  where complain = throwError $ "Trying to access a constructor from another module: " <+> pretty qn


-- | Class for things that can be converted to core syntax
class ToCore a where
  type CoreOf a
  toCore :: a -> ToCoreM (CoreOf a)


-- | Convert some term to Agda's core representation.
convert :: ToCore a => Defs -> Cons -> a -> Either Doc (CoreOf a)
convert defs cons t = runReaderT (runToCore $ toCore t) (defs, cons)

toSubst :: [Term] -> Core.Subst
toSubst = foldr Core.SCons Core.SNil

instance ToCore I.Term where
  type CoreOf I.Term = Term

  toCore (I.Var k es) = (TVar (var k) `tApp`) <$> toCore es
    where var :: Int -> Index
          var !n | n <= 0 = Scope.inHere
          var !n          = Scope.inThere (var (n - 1))

  toCore (I.Lam ai t) = TLam <$> toCore t

  -- TODO(flupe): add literals once they're added to core
  toCore (I.Lit l) = throwError "literals not supported"

  toCore (I.Def qn es) = tApp <$> (TDef <$> lookupDef qn) <*> toCore es

  toCore (I.Con ch ci es)
    | Just args <- allApplyElims es
    = do
        -- @l@ is the amount of arguments missing from the application.
        -- we need to eta-expand manually @l@ times to fully-apply the constructor.
        let l  = length (I.conFields ch) - length es
        let vs = reverse $ take l $ TVar <$> iterate Scope.inThere Scope.inHere
        con <- lookupCons (I.conName ch)

        t <- TCon con . toSubst . (++ vs) <$> toCore (raise l args)

        -- in the end, we bind @l@ fresh variables
        pure (iterate TLam t !! l)

  toCore I.Con{} = throwError "cubical endpoint application to constructors not supported"

  toCore (I.Pi dom codom) = TPi <$> toCore dom <*> toCore codom

  toCore (I.Sort s) = TSort <$> toCore s

  toCore (I.Level l) = throwError "level expressions not supported"

  -- the following cases shouldn't happen, but let's document errors properly
  toCore I.MetaV{}    = throwError "encountered metavariable"
  toCore I.DontCare{} = throwError "encountered DontCare constructor"
  toCore I.Dummy{}    = throwError "encountered Dummy constructor"


instance ToCore I.Level where
  type CoreOf I.Level = Natural
  toCore (I.Max c []) = pure $ fromInteger c
  toCore l            = throwError $ "level" <+> pretty l <+> "not supported"


instance ToCore I.Univ where
  type CoreOf I.Univ = Natural -> Sort
  toCore I.UType = pure STyp
  toCore I.UProp = throwError "Prop universes not supported"
  toCore I.USSet = throwError "SSet universes not supported"


instance ToCore I.Sort where
  type CoreOf I.Sort = Sort
  toCore (I.Univ univ l) = toCore univ <*> toCore l
  toCore s = throwError $ "sort" <+> pretty s <+> " not supported"


instance ToCore I.Type where
  type CoreOf I.Type = Core.Type
  toCore (I.El sort t) = Core.El <$> toCore sort <*> toCore t


instance (Subst a, ToCore a) => ToCore (I.Abs a) where
  type CoreOf (I.Abs a) = CoreOf a
  toCore = toCore . absBody


instance ToCore a => ToCore (Arg a) where
  type CoreOf (Arg a) = CoreOf a
  toCore = toCore . unArg


-- TODO(flupe): enforce that there are no weird modalities in the arg (e.g: disallow irrelevance)
instance ToCore a => ToCore (I.Dom a) where
  type CoreOf (I.Dom a) = CoreOf a
  toCore = toCore . unDom


instance ToCore I.Elim where
  type CoreOf I.Elim = Term
  toCore (I.Apply x)   = toCore x
  toCore (I.Proj _ qn) = TDef <$> lookupDef qn
  toCore I.IApply{}    = throwError "cubical endpoint application not supported"


instance ToCore a => ToCore [a] where
  type CoreOf [a] = [CoreOf a]
  toCore = traverse toCore

