module Main where

import Debug.Trace

import Data.Either (partitionEithers)
import Data.Foldable (for_, foldl')
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Version (showVersion)

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT))
import Control.DeepSeq ( NFData(..) )

import Agda.Main (runAgda')
import Agda.TypeChecking.Pretty (text, prettyTCM, (<+>), Doc)
import Agda.Compiler.Backend (Flag, IsMain(..), Backend', Backend_boot(Backend), Backend'_boot(Backend'),
 TCM, Recompile(Recompile, Skip), reportSDoc)
import Agda.Compiler.Backend qualified as Internal
import Agda.Syntax.Internal ( clausePats, Clause(clauseBody), Abs (unAbs) )
import Agda.Syntax.Internal qualified as Internal
import Agda.TypeChecking.Telescope qualified as Internal
import Agda.TypeChecking.Substitute qualified as Internal
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)

import Agda.Core.PrettyPrint (prettyCore, NameMap(..))
import Agda.Core.ToCore (convert, ToCoreGlobal(..))
import Agda.Core.UtilsH
    ( indexToNat,
      listToUnitList,
      boxInDoc,
      lineInDoc,
      reportSDocFailure,
      reportSDocWarning )
import Agda.Core.Syntax.Context ( Context(CtxEmpty) )
import Agda.Core.Syntax.Signature qualified as Core
import Agda.Core.Syntax.Term qualified as Core
import Agda.Core.TCM.TCM qualified as Core
import Agda.Core.Prelude qualified as Core
import Agda.Core.Checkers.TypeCheck (checkType)

import Agda.Utils.Either (maybeRight)
import Agda.Utils.Maybe (mapMaybe, isNothing, fromMaybe)
import Agda.Utils.IORef (IORef, newIORef, readIORef, writeIORef, modifyIORef')
import Agda.Utils.Impossible (__IMPOSSIBLE__)

import Agda.Syntax.Common.Pretty qualified as Pretty

import Scope.Core as Scope ()
import Scope.In as Scope ( Index(..), inHere, inThere )

import Paths_agda_core ( version )

import System.Console.ANSI
    ( getTerminalSize,
      setSGR,
      Color(..),
      ColorIntensity(Vivid),
      ConsoleIntensity(BoldIntensity),
      ConsoleLayer(Foreground),
      SGR(SetColor, SetConsoleIntensity) )
import Agda.Interaction.Options (OptDescr(Option), ArgDescr(NoArg))
import GHC.Natural (Natural)
import Foreign.Marshal (mallocArray0)
import Control.Monad (mzero)
import Control.Monad.Except (ExceptT, MonadError (throwError), liftEither, runExcept, runExceptT)
import Agda.TypeChecking.SizedTypes.WarshallSolver (Error)
import qualified Agda.TypeChecking.Primitive as I
import Agda.Benchmarking (Phase(Definition))
import Agda.Compiler.JS.Compiler (global)

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
-- main function

main :: IO ()
main = runAgda' [Backend backend]

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
-- command line options
data AgdaCoreOptions = Options {
  optIsEnabled  :: Bool,
  optTypecheck :: Bool
  }

instance NFData AgdaCoreOptions where
  rnf :: AgdaCoreOptions -> ()
  rnf _ = ()

defaultOptions :: AgdaCoreOptions
defaultOptions = Options {
   optIsEnabled  = True,
   optTypecheck = True
   }

disableOpt :: Flag AgdaCoreOptions
disableOpt opts = return opts { optIsEnabled = False }

disableTypecheck :: Flag AgdaCoreOptions
disableTypecheck opts = return opts { optTypecheck = False }

agdaCoreCommandLineFlags :: [OptDescr (Flag AgdaCoreOptions)]
agdaCoreCommandLineFlags =
  [
  Option ['d'] ["disable-backend"] (NoArg disableOpt) "Disable backend",
  Option [] ["no-typecheck"] (NoArg disableTypecheck) "Disable typechecking from agda-core (Agda still typecheck)"
  ]

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
-- The backend

-- backend :: Backend' opts env menv mod def
backend :: Backend' AgdaCoreOptions ACEnv ACMEnv ACMod ACSyntax
backend = Backend'
  { backendName           = "agda-core"
  , backendVersion        = Just $ Text.pack $ showVersion version
  , options               = defaultOptions
  , commandLineFlags      = agdaCoreCommandLineFlags
  , isEnabled             = optIsEnabled
  , preCompile            = agdaCorePreCompile             -- 1 create global env
  , postCompile           = agdaCorePostCompile            -- 5 nothing
  , preModule             = agdaCorePreModule              -- 2 what is compiled
  , postModule            = agdaCorePostModule             -- 4 typechecking
  , compileDef            = agdaCoreCompile                -- 3 translates internal to agda-core
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _       -> pure True
  , backendInteractTop    = Nothing
  , backendInteractHole   = Nothing
  }
{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
-- PreCompile
-- create an IO reference used as the global environement

data PreSignature = PreSignature {
  preSigDefs      :: Map Natural Core.Definition,
  preSigData      :: Map Natural Core.Datatype,
  preSigCons      :: Map (Natural, Natural) Core.Constructor
}

data ACEnv = ACEnv {
  toCoreGlobal          :: IORef ToCoreGlobal,     -- Internal.QNames to definitions/datatypes/constructors ID
  toCoreNames           :: IORef NameMap,          -- remember definition/datatypes ID to the names
  toCorePreSignature    :: IORef PreSignature,
  toCoreCounterID       :: IORef Index,
  toCoreIsTypechecking  :: Bool
  }

agdaCorePreCompile :: AgdaCoreOptions -> TCM ACEnv
agdaCorePreCompile Options{optTypecheck} = do
  tcg     <- liftIO $ newIORef $ ToCoreGlobal Map.empty Map.empty Map.empty Map.empty
  names   <- liftIO $ newIORef $ NameMap Map.empty Map.empty Map.empty Map.empty
  preSig  <- liftIO $ newIORef $ PreSignature Map.empty Map.empty Map.empty
  i       <- liftIO $ newIORef Zero
  pure $ ACEnv { toCoreGlobal          = tcg
               , toCoreNames           = names
               , toCorePreSignature    = preSig
               , toCoreCounterID       = i
               , toCoreIsTypechecking  = optTypecheck
               }

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
-- PreModule (actions for modules before compilation)
-- just skips agda.primitive and compile every other module

type ACMEnv = ()
type ACMod  = ()

agdaCorePreModule :: ACEnv -> IsMain -> TopLevelModuleName -> Maybe FilePath -> TCM (Recompile ACMEnv ACMod)
agdaCorePreModule _ _ tlm _ =
  -- skip agda.primitive
  -- TODO: do it in a clean way
  let name = show (Pretty.pretty tlm) in
  case name of
    "Agda.Primitive" -> pure $ Skip ()
    _ -> do
      reportSDoc "agda-core.check" 2 lineInDoc
      liftIO $ setSGR [ SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Magenta ]
      reportSDoc "agda-core.check" 1 . boxInDoc $ "Compiling module " <> show (Pretty.pretty tlm)
      liftIO $ setSGR []
      reportSDoc "agda-core.check" 2 lineInDoc
      pure $ Recompile ()


{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
-- Compilation
-- translate each definition from agda internal syntax to agda-core syntax
-- and add it to the global environement

type ACSyntax = Either String Core.Definition


agdaCoreCompile :: ACEnv -> ACMEnv -> IsMain -> Internal.Definition -> TCM ACSyntax
agdaCoreCompile env _ _ def = do
  let ACEnv{toCoreGlobal = ioTcg, toCoreCounterID = ioIndex, toCoreNames = ioNames, toCorePreSignature = ioPreSig } = env
      Internal.Defn{defName, defType, theDef} = def

  let name = show $ Pretty.pretty $ last $ Internal.qnameToList0 defName            -- name of term that we are compiling
  reportSDoc "agda-core.check" 2 $ text $ "Compilation of " <> name <> " :"

  ToCoreGlobal {
    globalDefs = tcg_defs, globalDatas = tcg_datas, globalRecs = tcg_recs,
    globalConsData = tcg_cons}                                        <- liftIO $ readIORef ioTcg
  NameMap {nameDefs, nameData, nameRecs, nameCons}                    <- liftIO $ readIORef ioNames
  PreSignature {preSigDefs, preSigData, preSigCons}                   <- liftIO $ readIORef ioPreSig
  index                                                               <- liftIO $ readIORef ioIndex    -- index of our new definition

    -- if a datatype or record is encountered, add all constructors to the environement
    -- if a constructor is encountered, skip it to avoid conflict
  (ntcg, nnames)  <-  case theDef of
    Internal.Datatype{dataPars, dataIxs, dataCons} -> do
      constInfo <- Internal.getConstInfo defName
      let ntcg_datas  = Map.insert defName (index, (dataPars, dataIxs)) tcg_datas
          nnames_datas = Map.insert  (indexToNat index) name nameData
          tcg_data_cons = Map.fromList (zip dataCons (map (index,) (iterate Suc Zero)))
          ntcg_cons = Map.union tcg_cons tcg_data_cons
      reportSDoc "agda-core.check" 3 $ text "  Constructors:" <+> prettyTCM dataCons
      pure (ToCoreGlobal tcg_defs ntcg_datas ntcg_cons, NameMap nameDefs nnames_datas nameCons)
    Internal.Record{recPars, recConHead} -> do
      let conName = Internal.conName recConHead
      reportSDoc "agda-core.check" 3 $ text "  Constructor:" <+> prettyTCM conName

      let ntcg_recs = Map.insert defName (index, recPars) tcg_recs
          nnames_recs = Map.insert (indexToNat index) name nameRecs
      pure (ToCoreGlobal ntcg_defs tcg_datas tcg_cons, NameMap nnames_defs nameData nameCons)
    Internal.Constructor{} -> do
      let (dID, cID) = tcg_cons Map.! defName
      let nnames_cons = Map.insert (indexToNat dID, indexToNat cID) name nameCons
      pure (ToCoreGlobal tcg_defs tcg_datas tcg_cons, NameMap nameDefs nameData nnames_cons)
    _ -> do
      let nnames_defs = Map.insert (indexToNat index) name nameDefs
      let ntcg_defs = Map.insert defName index tcg_defs
      pure (ToCoreGlobal ntcg_defs tcg_datas tcg_cons, NameMap nnames_defs nameData nameCons)

  liftIO $ writeIORef ioTcg   ntcg
  liftIO $ writeIORef ioNames nnames
  liftIO $ writeIORef ioIndex (Suc index)

  defTypeDoc <- prettyTCM defType
  reportSDoc "agda-core.check" 4 $ text "  Agda type: " <> prettyTCM defType
  reportSDoc "agda-core.check" 5 $ text "  Agda definition: " <> text (show $ Pretty.pretty theDef)
  -- reportSDoc "agda-core.check" 5 $ text "  Agda definition: " <> text (show theDef)


  case convert ntcg def of
    -- Failed to convert `def` with the ToCoreGlobal `ntcg`
    Left e     -> do
      reportSDocFailure "agda-core.check"   $ text $ "  Failed to convert '" <> name <> "' to core syntax:"
      reportSDocFailure "agda-core.check"   $ text "    " <> pure e
      return $ throwError name
    Right def'-> do
      let Core.Definition{defType = ty', theDef = defn'} = def'
      reportSDoc "agda-core.check" 4 $ text $ "  Agda Core Type: " <> prettyCore nnames ty'
      reportSDoc "agda-core.check" 4 $ text $ "  Agda Core Definition: " <> prettyCore nnames defn'

      reportSDoc "agda-core.debug" 10 $ text ("Index of definition being translated: " <> show (indexToNat index))
      reportSDoc "agda-core.debug" 10 $ text ""

      case defn' of
        Core.FunctionDefn _  -> liftIO $ writeIORef ioPreSig $
          PreSignature
            { preSigDefs = Map.insert (indexToNat index) def' preSigDefs
            , preSigData = preSigData
            , preSigCons = preSigCons
            }
        Core.DatatypeDefn dt -> liftIO $ writeIORef ioPreSig $
          PreSignature
            { preSigDefs = preSigDefs
            , preSigData = Map.insert (indexToNat index) dt preSigData
            , preSigCons = preSigCons
            }
        Core.ConstructorDefn cons -> do
          -- It should not matter here whether one uses `tcg_cons` (old one) or `globalConsData ntcg` (new one), but let's use the new one to be safe
          let (dID, cID) = globalConsData ntcg Map.! defName
          liftIO $ writeIORef ioPreSig $
            PreSignature
              {  preSigDefs = preSigDefs
              , preSigData = preSigData
              , preSigCons = Map.insert (indexToNat dID, indexToNat cID) cons preSigCons
              }
      return $ pure def'


{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
-- PostModule
-- do the typechecking
preSignatureToSignature :: PreSignature -> Core.Signature
preSignatureToSignature PreSignature {preSigDefs, preSigData, preSigCons}  =  do
  let datas i  = case preSigData Map.!? indexToNat i of
        Just dt -> dt
        _ -> __IMPOSSIBLE__

  let defns i  = case preSigDefs Map.!? indexToNat i of
        Just  Core.Definition{defType = ty, theDef = Core.FunctionDefn body} -> (ty, Core.FunctionDef body)
        _ -> __IMPOSSIBLE__

  let cons d c = case preSigCons Map.!? (indexToNat d, indexToNat c) of
        Just ct -> ct
        _ -> __IMPOSSIBLE__
  Core.Signature datas defns cons


agdaCorePostModule :: ACEnv -> ACMEnv -> IsMain -> TopLevelModuleName -> [ACSyntax] -> TCM ACMod
agdaCorePostModule ACEnv{toCoreIsTypechecking = False} _ _ _ _ = pure ()
agdaCorePostModule ACEnv{toCorePreSignature = ioPreSig} _ _ tlm defs = do
  reportSDoc "agda-core.check" 2 lineInDoc
  liftIO $ setSGR [ SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Cyan ]
  reportSDoc "agda-core.check" 1 . boxInDoc $ "Typechecking module " <> show (Pretty.pretty tlm)
  liftIO $ setSGR []
  reportSDoc "agda-core.check" 2 lineInDoc
  reportSDocWarning "agda-core.check" 1 $ text "Warning : Typechecking backend is in developpement"
  reportSDocWarning "agda-core.check" 1 $ text "__IMPOSSIBLE__ will be called if terms for which compilation failed are called"
  for_ defs \def -> do
    case def of
      Left n -> reportSDocFailure "agda-core.check" $ text $ "Skipped " <> n <> " :  term not compiled"
      Right Core.Definition{ defName, theDef = Core.FunctionDefn funBody, defType } -> do
        reportSDoc "agda-core.check" 2 $ text $ "Typechecking of " <> defName <> " :"
        preSig <- liftIO $ readIORef ioPreSig
        let sig = preSignatureToSignature preSig
        let fl  = Core.More fl
            env = Core.MkTCEnv sig fl
        case Core.runTCM (checkType CtxEmpty funBody defType) env of
              Left err -> reportSDoc "agda-core.check" 3 $ text $ "  Type checking error: " ++ err
              Right ok -> reportSDoc "agda-core.check" 3 $ text "  Type checking success"
      Right Core.Definition{ defName } ->
        reportSDocWarning "agda-core.check" 2 $ text $ "Skipped " <> defName <> " : not a function"


{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
-- PostCompile
-- do nothing

agdaCorePostCompile :: ACEnv -> IsMain -> Map TopLevelModuleName ACMod -> TCM ()
agdaCorePostCompile _ _ _ = pure ()

