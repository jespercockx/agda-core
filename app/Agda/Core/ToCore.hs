{-# LANGUAGE TypeFamilies, OverloadedStrings #-}

-- | Conversion from Agda's internal syntax to core representation
module Agda.Core.ToCore
  ( ToCore(..)
  , ToCoreM
  , ToCoreGlobal(..)
  , convert
  ) where

import Control.Monad (when, forM)
import Control.Monad.Reader (ReaderT, runReaderT, MonadReader, asks)
import Control.Monad.Except (MonadError(throwError), withError)
import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import Numeric.Natural (Natural)

import Agda.Syntax.Common ( Arg(unArg) )
import Agda.Syntax.Abstract.Name (QName, showQNameId, uglyShowName, qnameName)
import Agda.Syntax.Internal (lensSort, unDom, unEl)
import Agda.Syntax.Internal.Elim (allApplyElims, splitApplyElims)
import Agda.Syntax.Common.Pretty ( Doc, Pretty(pretty), (<+>), nest, multiLineText )
import Agda.TypeChecking.Substitute ()
import Agda.TypeChecking.Substitute.Class (Subst, absBody, raise)
import Agda.Utils.Maybe (fromMaybeM, whenNothingM, isNothing, isJust, caseMaybe, fromMaybe)
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

import Agda.Core.UtilsH (listToUnitList, indexToNat, indexToInt, traceCyan)


import Scope.In (Index)
import Scope.In qualified as Scope
import Agda.Utils.Either (maybeRight)
import qualified Agda.Syntax.Common.Pretty as Pretty
import System.IO (withBinaryFile)
import Agda.Compiler.Backend (Definition(defType), reportSDoc)
import Control.Exception (throw)

import Agda.TypeChecking.Pretty (PrettyTCM(prettyTCM))

import Agda.Syntax.Common.Pretty(text, render)



universeLevelFromSort :: I.Sort -> Integer
universeLevelFromSort (I.Univ I.UType (I.Max i [])) = i
universeLevelFromSort _ = error "unsupported universe level"

-- TODO(flupe): move this to Agda.Core.Syntax
-- | Apply a core term to elims
tApp :: Term -> [Term] -> Term
tApp t []     = t
tApp t (e:es) = TApp t e `tApp` es


-- | Global definitions are represented as a mapping from @QName@s
--   to proofs of global def scope membership.
--   Datatypes are stored with their amount of parameters/indices
--   Record types are stored with their amount of parameters
--   Datatype/record constructors are stored with their datatype/record index
data ToCoreGlobal = ToCoreGlobal { globalDefs      :: Map QName Index,
                                   globalDatas     :: Map QName (Index, (Nat, Nat)),
                                   globalRecs      :: Map QName (Index, Nat),
                                   -- Nothing if it is a record constructor
                                   -- (Just i) if it is a datatype constructor
                                   globalCons      :: Map QName (Index, Maybe Index)}

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

asksRec :: (Map QName (Index, Nat) -> a) -> ToCoreM a
asksRec = asks . (. \ToCoreGlobal{globalRecs} -> globalRecs)


equalsIndex :: Index -> Index -> Bool
equalsIndex Scope.Zero Scope.Zero         = True
equalsIndex Scope.Zero (Scope.Suc _)      = False
equalsIndex (Scope.Suc _) Scope.Zero      = False
equalsIndex (Scope.Suc x) (Scope.Suc y)   = equalsIndex x y

minusIndex :: Index -> Index -> Index
minusIndex Scope.Zero    _       = Scope.Zero
minusIndex x       Scope.Zero    = x
minusIndex (Scope.Suc x) (Scope.Suc y) = minusIndex x y

-- Given an index i, tests whether `i` is an index pointing to a record type definition
indexInRecs :: Index -> ToCoreM Bool
indexInRecs i = asksRec (any (\(j, _) -> equalsIndex j i) . Map.elems)

asksCon :: (Map QName (Index, Maybe Index) -> a) -> ToCoreM a
asksCon = asks . (. \ToCoreGlobal{globalCons} -> globalCons)

-- | Lookup a definition name in the current module.
lookupDef :: QName -> ToCoreM (Maybe Index)
lookupDef qn = asksDef (Map.!? qn)

-- | Lookup a datatype name in the current module.
lookupData :: QName -> ToCoreM (Maybe (Index, (Nat, Nat)))
lookupData qn = asksData (Map.!? qn)

-- | Lookup a record name in the current module.
lookupRec :: QName -> ToCoreM (Maybe (Index, Nat))
lookupRec qn = asksRec (Map.!? qn)

-- | Lookup a constructor name in the current module.
lookupCon :: QName -> ToCoreM (Maybe (Index, Maybe Index))
lookupCon qn = asksCon (Map.!? qn)


getRecordIndexFromProjIndex :: Index -> ToCoreM Index
getRecordIndexFromProjIndex Scope.Zero = do
  indexInRecs Scope.Zero >>= \case
    True -> return Scope.Zero
    False -> throwError "Could not get record index from projection index"
getRecordIndexFromProjIndex (Scope.Suc i') = do
  indexInRecs (Scope.Suc i') >>= \case
    True -> return (Scope.Suc i')
    False -> getRecordIndexFromProjIndex i'

createTAppAndTProj :: Term -> [(I.Elim, Term)] -> ToCoreM Term
createTAppAndTProj t [] = return t
createTAppAndTProj t ((I.Apply _, compiledElim):elims) =
  TApp t compiledElim `createTAppAndTProj` elims
-- When compiling an I.Proj _ _, the result must be a TDef `id`
createTAppAndTProj t ((I.Proj _ _, TDef projFuncId):elims) = do
  recordIndex <- getRecordIndexFromProjIndex projFuncId
  finalTerm <- createTAppAndTProj t elims
  return (TProj recordIndex finalTerm projFuncId)
createTAppAndTProj t _ =
  error ("This case is impossible: either compiling an I.Proj _ _ did not " ++
         "return a TDef, which is impossible, or the error '[When translating " ++
         "an Elim] cubical endpoint application not supported' should be " ++
         "thrown earlier instead")


teleToList :: I.Tele a -> [a]
teleToList I.EmptyTel = []
teleToList (I.ExtendTel a (I.Abs _ tel)) = a : teleToList tel
teleToList (I.ExtendTel a (I.NoAbs _ tel)) = error "Impossible case: Abs is never NoAbs so this error cannot happen"



-- | Class for things that can be converted to core syntax
class ToCore a where
  type CoreOf a
  toCore :: a -> ToCoreM (CoreOf a)


-- | Convert some term to Agda's core representation.
convert :: ToCore a => ToCoreGlobal -> a -> Either Doc (CoreOf a)
convert tcg t = runReaderT (runToCore $ toCore t) tcg

toTermS :: [Term] -> Core.TermS
toTermS = foldr Core.TSCons Core.TSNil


-- | Constructs a 'Core.TermS' from a list of eliminations and the total number of arguments.
--
-- @elims@: A list of eliminations (e.g., function applications or projections).
--          The length of @elims@ represents the number of arguments that are actually applied
--
-- @missing@: The number of arguments missing for a fully applied term.
--               We construct @missing@ amount of extra arguments 
--               as deBruijn indices (e.g., @TVar 0, TVar 1, ...@).
-- mkTermS :: I.Elims -> Int -> ToCoreM Core.TermS
-- mkTermS elims missing = do
--   listOfCoreTerms <- fmap (++ additionalVars) (toCore (raise missing elims))
--   return (foldr Core.TSCons Core.TSNil listOfCoreTerms)

-- Helper for toCore (I.Def)
compileToTDataOrTRec :: [I.Elim] -> Index -> Int -> Int -> Bool -> ToCoreM Term
compileToTDataOrTRec elims idx fullAmountOfParams fullAmountOfIndices toTData = do

  let givenParameterList = take fullAmountOfParams elims
  let givenIndexList = drop fullAmountOfParams elims -- has length 0 if any parameters are missing

  let missingParams = fullAmountOfParams - length givenParameterList
  let missingIndices = fullAmountOfIndices - length givenIndexList
  let totalMissing = missingParams + missingIndices

  -- we get [TVar 2, TVar 1, TVar 0, ...] of length @totalMissing@
  let additionalVars = reverse $ take totalMissing $ TVar <$> iterate Scope.inThere Scope.inHere
  compiledArgs <- fmap (++ additionalVars) (toCore (raise totalMissing elims))

  let paramTermS = toTermS (take fullAmountOfParams compiledArgs)
  let idxTermS = toTermS (drop fullAmountOfParams compiledArgs)

  let baseTerm =
        if toTData
        then TData idx paramTermS idxTermS
        else TRec idx paramTermS
  -- in the end, we have (TLam (TLam (TLam ...))) of depth `totalMissing`
  return (iterate TLam baseTerm !! totalMissing)
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
    = do
        lookupDef qn >>= \case
          Just idx -> do
            let def = TDef idx
            coreEs <- toCore es
            createTAppAndTProj def (zip es coreEs)
          Nothing -> do
            lookupData qn >>= \case
              Just (idx, (fullAmountOfParams, fullAmountOfIndices)) ->
                compileToTDataOrTRec es idx fullAmountOfParams fullAmountOfIndices True
              Nothing -> lookupRec qn >>= \case
                Nothing -> throwError $ "[When compiling an I.Def] Trying to access an unknown definition: " <+> pretty qn
                Just (idx, fullAmountOfParams) ->
                  compileToTDataOrTRec es idx fullAmountOfParams 0 False

  toCore (I.Con ch _ es)
    | Just args <- allApplyElims es
    = lookupCon (I.conName ch) >>= \case
        Nothing -> throwError $ "[When compiling a Con] Trying to access an unknown constructor: " <+> pretty (I.conName ch)
        Just (dt , con) -> do
          -- @l@ is the amount of arguments missing from the application.
          -- we need to eta-expand manually @l@ times to fully-apply the constructor.
          let l  = length (I.conFields ch) - length es
          -- Construct @l@ additional deBruijn indices
          let additionalVars = reverse $ take l $ TVar <$> iterate Scope.inThere Scope.inHere

          let constructor = maybe (TRecCon dt) (TDataCon dt) con
          t <- constructor . toTermS . (++ additionalVars) <$> toCore (raise l args)
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

    I.FunctionData{_funProjection = Right p} -- the FunctionDefn being declared is a record projection function
      | Just qn <- I.projProper p
        -> do
            --Looking up as a record must succeed
            _ <- lookupRec qn >>= \case
                  Nothing -> throwError $ "Trying to access an unknown record definition: " <+> pretty qn
                  Just (recordIndex, _) -> pure recordIndex
            throwError "Record projection functions are not compiled in Agda Core"
    I.FunctionData{}
      -> throwError "unsupported case (shouldn't happen)"


toCoreDefn (I.DatatypeDefn dt) ty =
  withError (\e -> multiLineText $ "datatype definition failure: \n" <> Pretty.render (nest 1 e)) $ do
  let I.DatatypeData{ _dataPars  = pars,
                      _dataIxs   = ixs,
                      _dataCons  = cons,
                      _dataSort  = sort} = dt
  -- let univLevel = universeLevelFromSort sort
  -- traceMagenta ("datatypedefn universe level from _dataSort " ++ show univLevel)
  sort' <- toCore sort
  let I.TelV{theTel = internalParsTel, theCore = ty1} = I.telView'UpTo pars ty
  let I.TelV{theTel = internalIxsTel}                 = I.telView'UpTo ixs  ty1
  parsTel <- toCore internalParsTel
  ixsTel <- toCore internalIxsTel
  cons_dt_indexes <- traverse (\qn -> lookupCon qn >>= \case
    Nothing -> throwError $ "[When compiling a DataTypeDefn] Trying to access an unknown constructor: " <+> pretty qn
    Just result -> pure result
    ) cons
  let cons_indexes = map (fromMaybe Scope.Zero . snd) cons_dt_indexes
  let d = Core.Datatype{  dataSort              = sort',
                          dataParTel            = parsTel,
                          dataIxTel             = ixsTel,
                          dataConstructors      = cons_indexes}
  return $ Core.DatatypeDefn d

toCoreDefn (I.RecordDefn rd) ty =
  withError (\e -> multiLineText $ "constructor definition failure:\n" <> Pretty.render (nest 1 e)) $ do
    let I.RecordData{
      _recPars = pars,
      _recFields = fields,
      _recTel = recordTelescope
    } = rd
    let I.TelV{theTel = internalParsTel, theCore = typWithoutParams} = I.telView'UpTo pars ty

    let internalParsTelPretty = pretty internalParsTel
    let typWithoutParamsPretty = pretty typWithoutParams
    let recordTelescopePretty = pretty recordTelescope

    parsTel <- toCore internalParsTel

    -- TODO: (atejandev) The sort should actually be the one from the record, instead of always being 0
    -- (I.Var 0 []) is irrelevant and is just there to make sure that the resulting type is `Sort' I.Term`
    sort <- toCore (I.Univ I.UType (I.Max 0 ([] :: [I.PlusLevel' I.Term])))
    -- sort <- do
    --   case typWithoutParams of 
    --     I.El s _ -> toCore s

    fieldsIndices <- traverse ((\qn -> lookupDef qn >>= \case
            Nothing -> throwError $ "[When compiling a RecordDefn] Trying to access an unknown definition: " <+> pretty qn
            Just idx -> pure idx
          ) . unDom) fields

 -- Construct the function `recProjTypes` which gives the full type of each projection function
    let fieldTypesList = drop pars (teleToList recordTelescope) --for example, this is: [A ; B] for the record `Pair`
    coreFieldTypes <- traverse (\fieldTypSurface -> do

            Core.El recSortCore recTypeTermCore <- toCore typWithoutParams
            Core.El fieldSortCore fieldTypeTermCore <- toCore fieldTypSurface
            pure $
              Core.El
                (Core.piSort fieldSortCore recSortCore)
                (TPi (Core.El recSortCore recTypeTermCore) (Core.El fieldSortCore fieldTypeTermCore))
            ) fieldTypesList

    let fieldsIndicesWithTypes :: [(Index, Core.Type)]
        fieldsIndicesWithTypes = zip fieldsIndices coreFieldTypes

    let recProjTypeLambdaHelper fieldProjIndex ps = traceCyan
            (
              "internalParsTel: " ++ show internalParsTelPretty
                ++ "\ntypWithoutParams: " ++ show typWithoutParamsPretty
                ++ "\nrecordTelescope: " ++ show recordTelescopePretty
            )
                case ps of
          [] -> error "requested field index was not available in the list of pairs; should not happen"
          (keyIndex, val):t_ps | equalsIndex fieldProjIndex keyIndex -> val
                               | otherwise -> recProjTypeLambdaHelper fieldProjIndex t_ps

    let recProjTypeLambda fieldProjIndex = recProjTypeLambdaHelper fieldProjIndex fieldsIndicesWithTypes

    let r = Core.Record{ recSort = sort,
                         recParTel = parsTel,
                         recProjTypes = recProjTypeLambda}

    return $ Core.RecordDefn r

toCoreDefn (I.ConstructorDefn cs) ty =
  withError (\e -> multiLineText $ "constructor definition failure:\n" <> Pretty.render (nest 1 e)) $ do
  let I.ConstructorData{  _conPars  = pars,
                          _conArity = arity}  = cs
      I.TelV{ theCore = tyInd}                = I.telView'UpTo pars ty
      I.TelV{ theTel = internalIndTel,
              theCore = I.El{unEl = tyCon}}   = I.telView'UpTo arity tyInd
  indTel <- toCore internalIndTel
  case tyCon of
    I.Def _ elims ->  do
      caseMaybe (I.allApplyElims $ drop pars elims) (throwError "index using variable not in scope") $ \ixs_m -> do
          ixs <- toCore ixs_m
          let ixsTermS = toTermS ixs
          let c = Core.Constructor{ conIndTel = indTel,
                                    conIx     = ixsTermS}
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
  toCore (I.Proj _ qn) = do
    let m_idx = lookupDef qn >>= \case
          Nothing -> throwError $ "[When translating an Elim] Trying to access an unknown definition: " <+> pretty qn
          Just ident -> pure ident
    TDef <$> m_idx
  toCore I.IApply{} = throwError "[When translating an Elim] cubical endpoint application not supported"


instance ToCore a => ToCore [a] where
  type CoreOf [a] = [CoreOf a]
  toCore :: ToCore a => [a] -> ToCoreM [CoreOf a]
  toCore = traverse toCore

