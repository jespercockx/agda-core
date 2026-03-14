{-# LANGUAGE TypeFamilies, OverloadedStrings #-}
{-# OPTIONS_GHC -Wunused-imports #-}

-- | Conversion from Agda's internal syntax to core representation
module Agda.Core.ToCore
  ( ToCore(..)
  , Data(..)
  , Constructor(..)
  , ToCoreM
  , ToCoreGlobal(..)
  , convert
  ) where

import Debug.Trace

import Control.Monad (when)
import Control.Monad.Reader (ReaderT, runReaderT, MonadReader, asks)
import Control.Monad.State.Strict (StateT, runStateT, MonadState, gets, modify, state, lift)
-- import Control.Monad.State.Strict (StateT, runStateT, gets, modify, state)
import Control.Monad.Except (MonadError(throwError), withError)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Numeric.Natural (Natural)

import Agda.Syntax.Common ( Arg(unArg) )
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Internal (unDom, unEl)
import Agda.Syntax.Internal.Elim (allApplyElims)
import Agda.Syntax.Common.Pretty ( Doc, Pretty(pretty), (<+>), nest, multiLineText )
import Agda.TypeChecking.Substitute ()
import Agda.TypeChecking.Substitute.Class (Subst, absBody, raise)
import Agda.Syntax.Common ( Nat )

import Agda.TypeChecking.Monad  qualified as I
import Agda.Syntax.Internal     qualified as I
import qualified Agda.Syntax.Common.Pretty as Pretty
import Agda.TypeChecking.Substitute qualified as I
import Agda.TypeChecking.CompiledClause qualified as CC

import Agda.Core.Syntax.Term (Term(..), Sort(..))
import Agda.Core.Syntax.Term      qualified as Core
import Agda.Core.Syntax.Context   qualified as Core
import Agda.Core.Syntax.Signature qualified as Core
import Agda.Core.UtilsH (intToIndex)

import Scope.In (Index)
import Scope.In qualified as Scope
import Scope.Core (rbind)

import Agda.Utils.Either (maybeRight)
import Agda.Utils.Size
import Agda.Utils.Maybe (isNothing, isJust, caseMaybe)

-- TODO(flupe): move this to Agda.Core.Syntax
-- | Apply a core term to elims
tApp :: Term -> [Term] -> Term
tApp t []     = t
tApp t (e:es) = TApp t e `tApp` es

-- | Global definitions are represented as a mapping from @QName@s
--   to proofs of global def scope membership.

-- Representation of a datatype; stores the index of the datatype, and its parameter list size and index list size
data Data = Data Index Nat Nat

-- Representation of a constructor; stores its index within its datatype, and its datatype
data Constructor = Constructor Index Data

data ToCoreGlobal = ToCoreGlobal { globalDefs  :: Map QName Index,
                                   globalDatas :: Map QName Data,
                                   globalCons  :: Map QName Constructor}

-- keeping track of debruijn indices correspondence from agda syntax to agda core syntax
type OffsetMap = Map Int Int

instance MonadState OffsetMap ToCoreM where
  state f = ToCoreM $ lift (state f)

-- | Custom monad used for translating to core syntax.
--   Gives access to global terms
--   Translation may fail.
newtype ToCoreM a = ToCoreM { runToCore :: ReaderT ToCoreGlobal (StateT OffsetMap (Either Doc)) a }
  deriving newtype (Functor, Applicative, Monad, MonadError Doc)
  deriving newtype (MonadReader ToCoreGlobal)

asksDef :: (Map QName Index -> a) -> ToCoreM a
asksDef = asks . (.  \ToCoreGlobal{globalDefs} -> globalDefs)

asksData :: (Map QName Data -> a) -> ToCoreM a
asksData = asks . (. \ToCoreGlobal{globalDatas} -> globalDatas)

asksCon :: (Map QName Constructor -> a) -> ToCoreM a
asksCon = asks . (. \ToCoreGlobal{globalCons} -> globalCons)

-- | Lookup a definition name in the current module.
lookupDef :: QName -> ToCoreM (Maybe Index)
lookupDef qn = asksDef (Map.!? qn)

-- | Lookup a datatype name in the current module.
lookupData :: QName -> ToCoreM (Maybe Data)
lookupData qn = asksData (Map.!? qn)

-- | Lookup a constructor name in the current module.
lookupCon :: QName -> ToCoreM (Maybe Constructor)
lookupCon qn = asksCon (Map.!? qn)

withLocalState :: (OffsetMap -> OffsetMap) -> ToCoreM a -> ToCoreM a
withLocalState f action = do
  saved <- gets id
  modify f
  result <- action
  ToCoreM $ lift (state (\_ -> ((), saved)))  -- restore
  return result

-- Read a value from the map
lookupOffset :: Int -> ToCoreM (Maybe Int)
lookupOffset k = gets (Map.lookup k)

-- Insert/update a value
insertOffset :: Int -> Int -> ToCoreM ()
insertOffset k v = modify (Map.insert k v)

updateKeys :: (Int -> Int) -> ToCoreM ()
updateKeys f = modify (Map.mapKeys f)

updateValues :: (Int -> Int -> Int) -> ToCoreM ()
updateValues f = modify (Map.mapWithKey f)

updateDBMap :: Int -> Int -> ToCoreM ()
updateDBMap paramIndexAgda constructParamCount = do

  updateKeys (\index -> if (index > paramIndexAgda) then index + constructParamCount - 1 else index) -- all the keys referring to agda indices get increased to make room for the new constsructors parameters
  updateValues (\_ value -> value + constructParamCount)

  let listConsParamsCore = reverse $ take constructParamCount (iterate (+1) 0)
      listConsParams     = map (\x -> paramIndexAgda + x) listConsParamsCore
  mapM_ (\(index, indexCore) -> insertOffset index indexCore) (zip listConsParams listConsParamsCore) -- for each constructor param, a new variable is bound anew in agda core db context, so it needs to be updated from agda context
  return ()

-- | Class for things that can be converted to core syntax
class ToCore a where
  type CoreOf a
  toCore :: a -> ToCoreM (CoreOf a)

-- | Convert some term to Agda's core representation.
convert :: ToCore a => ToCoreGlobal -> a -> Either Doc (CoreOf a)
convert tcg t =
  fst <$> runStateT (runReaderT (runToCore $ toCore t) tcg) Map.empty

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

  toCore (I.Var k es) = do
      index <- maybe k id <$> lookupOffset k -- should always be found, id should never be hit
      (TVar (var index) `tApp`) <$> toCore es
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
        maybe_idx <- lookupDef qn
        case maybe_idx of
          Just idx -> do
            let def = TDef idx
            coreEs <- toCore es
            return (tApp def coreEs)
          --Otherwise, try looking up as datatype (must succeed, else fail with error message)
          Nothing -> do
            lookupData qn >>= \case
              Nothing -> throwError $ "Trying to access an unknown definition: " <+> pretty qn

              Just (Data idx amountOfParams amountOfIndices) -> do
                --always take all parameters
                paramTermS <- toTermS <$> toCore (take amountOfParams args)

                -- @m@ is the amount of arguments to the index list which are missing
                let indexListGiven = drop amountOfParams args
                let m = amountOfIndices - length indexListGiven

                -- Construct @m@ additional deBruijn indices
                -- so we get [TVar 2, TVar 1, TVar 0, ...] of length m
                let additionalVars = reverse $ take m $ TVar <$> iterate Scope.inThere Scope.inHere

                indexTermS <- toTermS . (++ additionalVars) <$> toCore (raise m indexListGiven)
                let tdata = TData idx paramTermS indexTermS

                -- in the end, we have (TLam (TLam (TLam ...))) of depth m
                return (iterate TLam tdata !! m)

  toCore I.Def{} = throwError "cubical endpoint application to definitions/datatypes not supported"

  toCore (I.Con ch _ es)
    | Just args <- allApplyElims es
    = lookupCon (I.conName ch) >>= \case
        Nothing -> throwError $ "Trying to access an unknown constructor: " <+> pretty (I.conName ch)
        Just (Constructor con (Data dt _ _)) -> do
          -- @l@ is the amount of arguments missing from the application.
          -- we need to eta-expand manually @l@ times to fully-apply the constructor.
          let l  = length (I.conFields ch) - length es
          -- Construct @l@ additional deBruijn indices
          let additionalVars = reverse $ take l $ TVar <$> iterate Scope.inThere Scope.inHere

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

-- Gets how many parameters were placed on the left
getLHSCount :: I.FunctionData -> Int
getLHSCount f = size $ (I.namedClausePats ((I._funClauses f) !! 0))

-- Unnest Pi type
unnestPi :: Int -> Core.Type -> ToCoreM Core.Type
unnestPi 0 ty = return ty
unnestPi n ty = case Core.unType ty of
  TPi _ dom -> unnestPi (n - 1) dom
  _ -> throwError "Incorrect Type, expected Pi"

-- Converts a CompiledClauses (Agda syntax) to a term (Agda Core syntax) (Both have case tree format instead of clause list format)
-- ty represents the type of the return of the case, and paramCount represents how many parameters have been pattern matched on the left hand side of the function clause
clauseToCore :: CC.CompiledClauses -> Core.Type -> Int -> ToCoreM Core.Term
clauseToCore (CC.Done args body) _ _ = toCore body
clauseToCore (CC.Case paramNum c) ty paramCount = do
  let branchList = Map.toList (CC.conBranches c)
  result <- lookupCon (fst (branchList !! 0))
  -- Getting the datatype of the constructor (assumes there is at least one constructor in the list, this will be an issue for something like the empty type)
  Constructor _ (Data dt params idcs) <- maybe (throwError "constructor not found") return result

  when (idcs > 0) $ throwError "Indexed datatypes are not yet supported"

  -- iRun is the run-time representation of the index scope. The result will always be `[]`, however, once indexed datatypes are supported this will be important.
  let iRun = iterate rbind [] !! idcs

  let indexAgda = paramCount - unArg paramNum - 1 -- debruijn index in the Agda syntax (paramNum is the number of the parameter, starting from the left)
  indexAgdaCore <- maybe (throwError "no mapping found") return =<< lookupOffset indexAgda -- getting corresponding agda core db index

  coreBranchList <- (mapM (uncurry (createBranch ty paramCount indexAgda)) branchList)
  let branches = foldr Core.BsCons Core.BsNil coreBranchList
  return $ TCase dt iRun (TVar $ intToIndex indexAgdaCore) branches ty
clauseToCore _ _ _ = throwError "not supported"

createBranch :: Core.Type -> Int -> Int -> QName -> CC.WithArity CC.CompiledClauses -> ToCoreM Core.Branch
createBranch ty paramCount paramIndexAgda name wthAr = do
  result <- lookupCon name
  Constructor constructor _ <- maybe (throwError "constructor not found") return result
  clause <- withLocalState id $ do -- do the update locally so changes in one branch do not causes changes in others
    updateDBMap paramIndexAgda (CC.arity wthAr) -- update the state, which contains a map of the correspondence between agda and agda core indices
    clauseToCore (CC.content wthAr) ty ((CC.arity wthAr) + paramCount - 1)
  return (Core.BBranch constructor (iterate rbind [] !! CC.arity wthAr) clause)


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

toCoreDefn (I.FunctionDefn def) ty =
  withError (\e -> multiLineText $ "function definition failure: \n" <> Pretty.render (nest 1 e)) $ do
  case def of
    -- case where you use lambda
    I.FunctionData{..}
      | isNothing (maybeRight _funProjection >>= I.projProper) -- discard record projections
      , Just compiledClauses      <- _funCompiled
      -> do
        -- translate the type of the function
        coretywithpi <- toCore ty
        -- gets the amount of variable on the LHS of each clause
        let lhscount = getLHSCount def 
        -- the type of the body of the function (which may need to be set as the type of a TCase) needs to be "pi unnested" as many times as variables have been put on the LHS
        corety <- unnestPi lhscount coretywithpi
        body <- withLocalState id $ do
          let nums = take lhscount (iterate (+1) 0)
          modify (\_ -> Map.fromList $ map (\x -> (x, x)) nums) -- update the state, which contains a map of the correspondence between agda and agda core indices
          clauseToCore compiledClauses corety lhscount
        Core.FunctionDefn <$> pure ((iterate TLam body) !! lhscount)
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
  cons_dt_indexes <- mapM (\mc -> maybe (throwError "constructor not found") return mc) =<< traverse lookupCon cons
  let cons_indexes = map (\(Constructor c _) -> c) cons_dt_indexes
  let d = Core.Datatype{  dataSort              = sort',
                          dataParTel            = parsTel,
                          dataIxTel             = ixsTel,
                          dataConstructors      = cons_indexes}
  return $ Core.DatatypeDefn d

toCoreDefn (I.RecordDefn rd) ty = throwError "records are not supported"

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

