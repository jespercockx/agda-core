{-# LANGUAGE TypeFamilies #-}

-- | Conversion from Agda's internal syntax to core representation
module Agda.Core.ToCore
  ( ToCore(..)
  , ToCoreM
  , Defs
  , convert
  ) where

import Control.Monad.Reader
import Control.Monad.Except (MonadError(throwError))
import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Internal qualified as I
import Agda.Core.Syntax

import Scope.In as Scope

-- TODO: preModuleHook to compute the entire moodule scope
--       (defs, cons, conArity)

type Defs = Map QName In

-- | Custom monad used for translating to core syntax.
--   Gives access to global defs.
--   Translation may fail.
newtype ToCoreM a = ToCoreM { runToCore :: ReaderT Defs (Either String) a }
  deriving newtype (Functor, Applicative, Monad, MonadError String)
  deriving newtype (MonadReader Defs)

lookupDef :: QName -> ToCoreM (Maybe In)
lookupDef qn = asks (Map.!? qn)

-- | Class for things that can be converted to core syntax
class ToCore a where
  type CoreOf a
  toCore :: a -> ToCoreM (CoreOf a)


instance ToCore I.Term where

  type CoreOf I.Term = Term

  toCore (I.Var k es) = (TVar (var k) `tApp`) <$> toCore es
    where var :: Int -> In
          var !n | n <= 0 = Scope.inHere
          var !n          = Scope.inThere (var (n - 1))

  -- TODO(flupe): handle NoAbs
  toCore (I.Lam ai (I.Abs _ t)) = TLam <$> toCore t

  -- TODO(flupe): enforce that there are no weird modalities in the arg (e.g: disallow irrelevance)
  toCore (I.Def qn es) = do
    def <- lookupDef qn >>= \case
      Nothing  -> throwError ""
      Just tgt -> pure $ TDef tgt
    (def `tApp`) <$> toCore es

  toCore _ = throwError "not supported"

-- | Apply a core term to elims
tApp :: Term -> Elims -> Term
tApp t []     = t
tApp t (e:es) = TApp t e `tApp` es


instance ToCore I.Elim where

  type CoreOf I.Elim = Elim

  toCore (I.Apply x)  = EArg <$> toCore (unArg x)
  toCore (I.Proj{})   = throwError "record projections not supported"
  toCore (I.IApply{}) = throwError "cubical endpoint application not supported"


instance ToCore I.Elims where

  type CoreOf I.Elims = Elims

  toCore = traverse toCore

convert :: ToCore a => Defs -> a -> Either String (CoreOf a)
convert defs t = runReaderT (runToCore $ toCore t) defs
