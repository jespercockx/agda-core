{-# LANGUAGE TypeFamilies, OverloadedStrings #-}

-- | Conversion from Agda's internal syntax to core representation
module Agda.Core.ToCore
  ( ToCore(..)
  , ToCoreM
  , ToCoreGlobal(..)
  , convert
  ) where

import Control.Monad (when)
import Control.Monad.Reader (ReaderT, runReaderT, MonadReader, asks)
import Control.Monad.Except (MonadError(throwError, catchError), withError)
import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import Numeric.Natural (Natural)

import Agda.Syntax.Common ( Arg(unArg) )
import Agda.Syntax.Abstract.Name (QName, showQNameId, uglyShowName, qnameName)
import Agda.Syntax.Internal (lensSort, unDom, unEl)
import Agda.Syntax.Internal.Elim (allApplyElims)
import Agda.Syntax.Common.Pretty ( Doc, Pretty(pretty), (<+>), nest, multiLineText )
import Agda.TypeChecking.Substitute ()
import Agda.TypeChecking.Substitute.Class (Subst, absBody, raise)
import Agda.Utils.Maybe (fromMaybeM, whenNothingM, isNothing, isJust, caseMaybe)
import Agda.Syntax.Common ( Nat )

import Data.Map.Strict qualified as Map
import Agda.TypeChecking.Monad  qualified as I
import Agda.Syntax.Internal     qualified as I
import Agda.TypeChecking.Substitute qualified as I
import Agda.TypeChecking.Telescope qualified as I


import Agda.Core.Syntax.Term (Term(..), Sort(..))
import Agda.Core.Syntax.Term      qualified as Core
import Agda.Core.Syntax.Context   qualified as Core
import Agda.Core.Syntax.Signature qualified as Core

import Agda.Core.UtilsH (listToUnitList, indexToNat, indexToInt)


import Scope.In (Index)
import Scope.In qualified as Scope
import Agda.Utils.Either (maybeRight)
import qualified Agda.Syntax.Common.Pretty as Pretty
import System.IO (withBinaryFile)
import Agda.Compiler.Backend (Definition(defType))
import Control.Exception (throw)

import Agda.TypeChecking.Pretty (PrettyTCM(prettyTCM))

import Agda.Syntax.Common.Pretty(text, render)


-- TODO(flupe): move this to Agda.Core.Syntax
-- | Apply a core term to elims
tApp :: Term -> [Term] -> Term
tApp t []     = t
tApp t (e:es) = TApp t e `tApp` es

-- | Global definitions are represented as a mapping from @QName@s
--   to proofs of global def scope membership.
--   Datatypes are stored in a different structure
--   Constructors are stored with their datatype
data ToCoreGlobal = ToCoreGlobal { globalDefs  :: Map QName Index,
                                   globalDatas :: Map QName (Index, (Nat, Nat)),
                                   globalCons  :: Map QName (Index, Index)}

-- | Custom monad used for translating to core syntax.
--   Gives access to global terms
--   Translation may fail.
newtype ToCoreM a = ToCoreM { runToCore :: ReaderT ToCoreGlobal (Either Doc) a }
  deriving newtype (Functor, Applicative, Monad, MonadError Doc)
  deriving newtype (MonadReader ToCoreGlobal)

asksDef :: (Map QName Index -> a) -> ToCoreM a
asksDef = asks . (.  \ToCoreGlobal{globalDefs} -> globalDefs)

asksData :: (Map QName (Index, (Nat, Nat)) -> a) -> ToCoreM a
asksData = asks . (. \ToCoreGlobal{globalDatas} -> globalDatas)

asksCon :: (Map QName (Index, Index) -> a) -> ToCoreM a
asksCon = asks . (. \ToCoreGlobal{globalCons} -> globalCons)

-- | Lookup a definition name in the current module.
--   Fails if the definition cannot be found.
lookupDef :: QName -> ToCoreM Index
lookupDef qn = fromMaybeM complain $ asksDef (Map.!? qn)
  where complain = throwError $ "Trying to access an unknown definition: " <+> pretty qn

-- | Lookup a datatype name in the current module.
--   Fails if the datatype cannot be found.
lookupData :: QName -> ToCoreM (Index, (Nat, Nat))
lookupData qn = fromMaybeM complain $ asksData (Map.!? qn)
  where complain = throwError $ "Trying to access an unknown datatype: " <+> pretty qn

-- | Lookup a constructor name in the current module.
--   Fails if the constructor cannot be found.
lookupCon :: QName -> ToCoreM (Index, Index)
lookupCon qn = fromMaybeM complain $ asksCon (Map.!? qn)
  where complain = throwError $ "Trying to access an unknown constructor: " <+> pretty qn


-- | Class for things that can be converted to core syntax
class ToCore a where
  type CoreOf a
  toCore :: a -> ToCoreM (CoreOf a)


-- | Convert some term to Agda's core representation.
convert :: ToCore a => ToCoreGlobal -> a -> Either Doc (CoreOf a)
convert tcg t = runReaderT (runToCore $ toCore t) tcg

toTermS :: [Term] -> Core.TermS
toTermS = foldr Core.TSCons Core.TSNil

{- ────────────────────────────────────────────────────────────────────────────────────────────── -}
{-                                      Instances of ToCore                                       -}
{- ────────────────────────────────────────────────────────────────────────────────────────────── -}

{- ────────────────────────────────────────────────────────────────────────────────────────────── -}
-- Terms
instance ToCore I.Term where
  type CoreOf I.Term = Term
  toCore :: I.Term -> ToCoreM Term

  toCore (I.Var k es) = (TVar (var k) `tApp`) <$> toCore es
    where var :: Int -> Index
          var !n | n <= 0 = Scope.inHere
          var !n          = Scope.inThere (var (n - 1))

  toCore (I.Lam ai t) = TLam <$> toCore t

  -- TODO(flupe): add literals once they're added to core
  toCore (I.Lit l) = throwError "literals not supported"

  toCore (I.Def qn es)
    | Just args <- allApplyElims es
    = do
      -- Try looking up as definition first
      catchError
        (do
          idx <- lookupDef qn
          let def = TDef idx
          coreEs <- toCore es
          return (tApp def coreEs)
        )
        --Otherwise, try looking up as datatype
        (\_ -> do
          (idx, (amountOfParams, amountOfIndices)) <- lookupData qn

          --always take all parameters
          paramTermS <- toTermS <$> toCore (take amountOfParams args)

          -- @m@ is the amount of arguments to the index list which are missing
          let indexListGiven = drop amountOfParams args
          let m = amountOfIndices - (length indexListGiven)

          -- Construct @m@ additional deBruijn indices
          -- so we get [TVar 2, TVar 1, TVar 0, ...] of length m
          let additionalVars = reverse $ take m $ TVar <$> iterate Scope.inThere Scope.inHere
          
          indexTermS <- toTermS . (++ additionalVars) <$> toCore (raise m indexListGiven)
          let tdata = TData idx paramTermS indexTermS

          -- in the end, we have (TLam (TLam (TLam ...))) of depth m
          return (iterate TLam tdata !! m)
        )

  toCore I.Def{} = throwError "cubical endpoint application to definitions/datatypes not supported"

  toCore (I.Con ch _ es)
    | Just args <- allApplyElims es
    = do
        -- @l@ is the amount of arguments missing from the application.
        -- we need to eta-expand manually @l@ times to fully-apply the constructor.
        let l  = length (I.conFields ch) - length es
        -- Construct @l@ additional deBruijn indices
        let additionalVars = reverse $ take l $ TVar <$> iterate Scope.inThere Scope.inHere
        (dt , con) <- lookupCon (I.conName ch)

        t <- TCon dt con . toTermS . (++ additionalVars) <$> toCore (raise l args)

        -- in the end, we bind @l@ fresh deBruijn indices
        pure (iterate TLam t !! l)

  toCore I.Con{} = throwError "cubical endpoint application to constructors not supported"

  toCore (I.Pi dom codom) = TPi <$> toCore dom <*> toCore codom

  toCore (I.Sort s) = TSort <$> toCore s

  toCore (I.Level l) = throwError "level expressions not supported"

  -- the following cases shouldn't happen, but let's document errors properly
  toCore I.MetaV{}    = throwError "encountered metavariable"
  toCore I.DontCare{} = throwError "encountered DontCare constructor"
  toCore I.Dummy{}    = throwError "encountered Dummy constructor"

{- ────────────────────────────────────────────────────────────────────────────────────────────── -}
-- Level
instance ToCore I.Level where
  type CoreOf I.Level = Natural
  toCore :: I.Level -> ToCoreM Natural
  toCore (I.Max c []) = pure $ fromInteger c
  toCore l            = throwError $ "level" <+> pretty l <+> "not supported"

{- ────────────────────────────────────────────────────────────────────────────────────────────── -}
-- Univ
instance ToCore I.Univ where
  type CoreOf I.Univ = Natural -> Sort
  toCore :: I.Univ -> ToCoreM (Natural -> Sort)
  toCore I.UType = pure STyp
  toCore I.UProp = throwError "Prop universes not supported"
  toCore I.USSet = throwError "SSet universes not supported"

{- ────────────────────────────────────────────────────────────────────────────────────────────── -}
-- Sort
instance ToCore I.Sort where
  type CoreOf I.Sort = Sort
  toCore :: I.Sort -> ToCoreM Sort
  toCore (I.Univ univ l) = toCore univ <*> toCore l
  toCore s = throwError $ "sort" <+> pretty s <+> " not supported"

{- ────────────────────────────────────────────────────────────────────────────────────────────── -}
-- Type
instance ToCore I.Type where
  type CoreOf I.Type = Core.Type
  toCore :: I.Type -> ToCoreM Core.Type
  toCore (I.El sort t) = Core.El <$> toCore sort <*> toCore t

{- ────────────────────────────────────────────────────────────────────────────────────────────── -}
-- Telescope
instance ToCore I.Telescope where
  type CoreOf I.Telescope = Core.Telescope
  toCore :: I.Telescope -> ToCoreM Core.Telescope
  toCore I.EmptyTel = pure Core.EmptyTel
  toCore (I.ExtendTel ty t) = Core.ExtendTel <$> toCore ty <*> toCore t


{- ────────────────────────────────────────────────────────────────────────────────────────────── -}
-- Defn (helper for Definition below)
toCoreDefn :: I.Defn -> I.Type -> ToCoreM Core.Defn
toCoreDefn (I.AxiomDefn _) _ =
  throwError "axioms are not supported"

toCoreDefn (I.DataOrRecSigDefn _ ) _ =
  throwError "encontered the unexpected case of a not fully defined data or record type"

toCoreDefn (I.GeneralizableVar _) _ =
  throwError "generalisable var are not supported"

toCoreDefn (I.AbstractDefn _) _ =
  throwError "abstract definition are not supported"

toCoreDefn (I.FunctionDefn def) _ =
  withError (\e -> multiLineText $ "function definition failure: \n" <> Pretty.render (nest 1 e)) $ do
  case def of
    -- case where you use lambda
    I.FunctionData{..}
      | isNothing (maybeRight _funProjection >>= I.projProper) -- discard record projections
      , [cl]      <- _funClauses
      , []        <- I.clausePats cl
      , Just body <- I.clauseBody cl
      -> Core.FunctionDefn <$> toCore body
    -- case with no pattern matching
    I.FunctionData{..}
      | isNothing (maybeRight _funProjection >>= I.projProper) -- discard record projections
      , [cl]      <- _funClauses
      , vars      <- I.clausePats cl
      , Just body <- I.clauseBody cl
      -- -> Core.FunctionDefn <$> toCore body
      -> throwError "only definitions via λ are supported"

    -- case with pattern matching variables
    I.FunctionData{..}
      | isNothing (maybeRight _funProjection >>= I.projProper) -- discard record projections
      , l      <- _funClauses
      -> throwError "pattern matching isn't supported"
    I.FunctionData{..}
      | isJust (maybeRight _funProjection >>= I.projProper) -- record projections case
      -> throwError "record projections aren't supported"
    I.FunctionData{}
      -> throwError "unsupported case (shouldn't happen)"

toCoreDefn (I.DatatypeDefn dt) ty =
  withError (\e -> multiLineText $ "datatype definition failure: \n" <> Pretty.render (nest 1 e)) $ do
  let I.DatatypeData{ _dataPars  = pars,
                      _dataIxs   = ixs,
                      _dataCons  = cons,
                      _dataSort  = sort} = dt
  sort' <- toCore sort
  let I.TelV{theTel = internalParsTel, theCore = ty1} = I.telView'UpTo pars ty
  let I.TelV{theTel = internalIxsTel}                 = I.telView'UpTo ixs  ty1
  parsTel <- toCore internalParsTel
  ixsTel <- toCore internalIxsTel
  cons_dt_indexes <- traverse lookupCon cons
  let cons_indexes = map snd cons_dt_indexes
  let d = Core.Datatype{  dataSort              = sort',
                          dataParTel            = parsTel,
                          dataIxTel             = ixsTel,
                          dataConstructors      = cons_indexes}
  return $ Core.DatatypeDefn d

toCoreDefn (I.RecordDefn rd) ty =
    throwError "records are not supported"

toCoreDefn (I.ConstructorDefn cs) ty =
  withError (\e -> multiLineText $ "constructor definition failure:\n" <> Pretty.render (nest 1 e)) $ do
  let I.ConstructorData{  _conPars  = pars,
                          _conArity = arity,
                          _conData  = dname}  = cs
      I.TelV{ theCore = tyInd}                = I.telView'UpTo pars ty
      I.TelV{ theTel = internalIndTel,
              theCore = I.El{unEl = tyCon}}   = I.telView'UpTo arity tyInd
  indTel <- toCore internalIndTel
  case tyCon of
    I.Def _ elims ->  do
      caseMaybe (I.allApplyElims $ drop pars elims) (throwError "index using variable not in scope") $ \ixs -> do
          ixs' <- toCore ixs
          let conIxs = foldr Core.TSCons Core.TSNil ixs'
          let c = Core.Constructor{ conIndTel = indTel,
                                    conIx     = conIxs}
          return $ Core.ConstructorDefn c
    _ -> do
      throwError $ "expected " <> Pretty.pretty tyCon <> "to be a Def"

toCoreDefn (I.PrimitiveDefn _) _ =
  throwError "primitive are not supported"

toCoreDefn (I.PrimitiveSortDefn _) _ =
  throwError "primitive sorts are not supported"


{- ────────────────────────────────────────────────────────────────────────────────────────────── -}
-- Definition
instance ToCore I.Definition where
  type CoreOf I.Definition = Core.Definition
  toCore :: I.Definition -> ToCoreM Core.Definition
  toCore def = do
    let I.Defn{defName, defType, theDef} = def
        name = show $ Pretty.pretty $ last $ I.qnameToList0 defName            -- name of term that we are compiling
    ty    <- withError (\e -> multiLineText $ "type conversion failed:\n" <> Pretty.render (nest 1 e)) $ toCore defType
    res   <- toCoreDefn theDef defType
    return Core.Definition{ defName = name,
                            defType = ty,
                            theDef = res}

{- ────────────────────────────────────────────────────────────────────────────────────────────── -}
-- Others
instance (Subst a, ToCore a) => ToCore (I.Abs a) where
  type CoreOf (I.Abs a) = CoreOf a
  toCore :: (Subst a, ToCore a) => I.Abs a -> ToCoreM (CoreOf (I.Abs a))
  toCore = toCore . absBody


instance ToCore a => ToCore (Arg a) where
  type CoreOf (Arg a) = CoreOf a
  toCore :: ToCore a => Arg a -> ToCoreM (CoreOf a)
  toCore = toCore . unArg


-- TODO(flupe): enforce that there are no weird modalities in the arg (e.g: disallow irrelevance)
instance ToCore a => ToCore (I.Dom a) where
  type CoreOf (I.Dom a) = CoreOf a
  toCore :: ToCore a => I.Dom a -> ToCoreM (CoreOf (I.Dom a))
  toCore = toCore . unDom


instance ToCore I.Elim where
  type CoreOf I.Elim = Term
  toCore :: I.Elim -> ToCoreM Term
  toCore (I.Apply x)   = toCore x
  --TODO (diode-lang) : Support projection as an Elim
  -- toCore (I.Proj _ qn) = TDef <$> lookupDefOrData qn
  toCore (I.Proj _ qn) = throwError "record projection not supported"
  toCore I.IApply{}    = throwError "cubical endpoint application not supported"


instance ToCore a => ToCore [a] where
  type CoreOf [a] = [CoreOf a]
  toCore :: ToCore a => [a] -> ToCoreM [CoreOf a]
  toCore = traverse toCore

