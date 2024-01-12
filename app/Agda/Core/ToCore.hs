{-# LANGUAGE TypeFamilies #-}

-- | Conversion from Agda's internal syntax to core representation
module Agda.Core.ToCore
  ( ToCore(..)
  , ToCoreM
  , Defs
  , convert
  ) where

import Control.Monad.Reader (ReaderT, runReaderT, MonadReader, asks)
import Control.Monad.Except (MonadError(throwError))
import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import Numeric.Natural (Natural)

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Internal (lensSort, unDom, unEl)
import Agda.TypeChecking.Substitute ()
import Agda.TypeChecking.Substitute.Class (Subst, absBody)
import Agda.Utils.Maybe (fromMaybeM)
import Agda.Utils.Lens ((^.))

import Data.Map.Strict      qualified as Map
import Agda.Syntax.Internal qualified as I

import Agda.Core.Syntax (Term(..), Elim(..), Elims, Sort(..))

import Scope.In (In)
import Scope.In qualified as Scope

-- | Global definitions are represented as a mapping from @QName@s
--   to proofs of global scope membership.
type Defs = Map QName In


-- TODO(flupe): move this to Agda.Core.Syntax
-- | Apply a core term to elims
tApp :: Term -> Elims -> Term
tApp t []     = t
tApp t (e:es) = TApp t e `tApp` es


-- | Custom monad used for translating to core syntax.
--   Gives access to global defs.
--   Translation may fail.
newtype ToCoreM a = ToCoreM { runToCore :: ReaderT Defs (Either String) a }
  deriving newtype (Functor, Applicative, Monad, MonadError String)
  deriving newtype (MonadReader Defs)
 

-- | Lookup a global definition in the current module.
--   Fails if the definition cannot be found there.
lookupDef :: QName -> ToCoreM In
lookupDef qn = fromMaybeM complain $ asks (Map.!? qn)
  where complain = throwError $ "Trying to access a definition from another module: " ++ prettyShow qn


-- | Class for things that can be converted to core syntax
class ToCore a where
  type CoreOf a
  toCore :: a -> ToCoreM (CoreOf a)


-- | Convert some term to Agda's core representation.
convert :: ToCore a => Defs -> a -> Either String (CoreOf a)
convert defs t = runReaderT (runToCore $ toCore t) defs


instance ToCore I.Term where
  type CoreOf I.Term = Term

  toCore (I.Var k es) = (TVar (var k) `tApp`) <$> toCore es
    where var :: Int -> In
          var !n | n <= 0 = Scope.inHere
          var !n          = Scope.inThere (var (n - 1))

  toCore (I.Lam ai t) = TLam <$> toCore t

  -- TODO(flupe): add literals once they're added to core
  toCore (I.Lit l) = throwError "literals not supported"

  toCore (I.Def qn es) = tApp <$> (TDef <$> lookupDef qn) <*> toCore es

  -- TODO(flupe)
  toCore (I.Con ch ci es) = throwError "constructors not supported"


  toCore (I.Pi dom codom) = TPi <$> toCore dom <*> toCore codom
        -- NOTE(flupe): we will need the sorts in the core syntax soon
        -- <$> toCore (dom   .^ lensSort)
        -- <*> toCore (codom .^ lensSort)

  toCore (I.Sort s) = TSort <$> toCore s

  toCore (I.Level l) = throwError "level expressions not supported"

  -- the following cases shouldn't happen, but let's document errors properly
  toCore I.MetaV{}    = throwError "encountered metavariable"
  toCore I.DontCare{} = throwError "encountered DontCare constructor"
  toCore I.Dummy{}    = throwError "encountered Dummy constructor"


instance ToCore I.Level where
  type CoreOf I.Level = Natural
  toCore (I.Max c []) = pure $ fromInteger c
  toCore l            = throwError $ "level " ++ prettyShow l ++ " not supported"


instance ToCore I.Univ where
  type CoreOf I.Univ = Natural -> Sort
  toCore I.UType = pure STyp
  toCore I.UProp = throwError "Prop universes not supported"
  toCore I.USSet = throwError "SSet universes not supported"


instance ToCore I.Sort where
  type CoreOf I.Sort = Sort
  toCore (I.Univ univ l) = toCore univ <*> toCore l
  toCore s = throwError $ "sort " ++ prettyShow s ++ " not supported"


instance ToCore I.Type where
  type CoreOf I.Type = CoreOf I.Term
  toCore = toCore . unEl


instance (Subst a, ToCore a) => ToCore (I.Abs a) where
  type CoreOf (I.Abs a) = CoreOf a
  toCore t = toCore (absBody t)


-- TODO(flupe): enforce that there are no weird modalities in the arg (e.g: disallow irrelevance)
instance ToCore a => ToCore (I.Dom a) where
  type CoreOf (I.Dom a) = CoreOf a
  toCore = toCore . unDom


instance ToCore I.Elim where
  type CoreOf I.Elim = Elim
  toCore (I.Apply x)  = EArg <$> toCore (unArg x)
  toCore I.Proj{}     = throwError "record projections not supported"
  toCore I.IApply{}   = throwError "cubical endpoint application not supported"


instance ToCore a => ToCore [a] where
  type CoreOf [a] = [CoreOf a]
  toCore = traverse toCore

