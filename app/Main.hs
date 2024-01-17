module Main where

import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Data.Either (partitionEithers)
import Data.Foldable (for_, foldl')
import Data.Map.Strict (Map)
import Data.Maybe (catMaybes, mapMaybe, isJust)
import Data.Version (showVersion)

import Data.Map.Strict qualified as Map

import Agda.Main
import Agda.TypeChecking.Pretty (text, prettyTCM, (<+>))
import Agda.Compiler.Backend
import Agda.Syntax.Internal
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import Agda.Core.ToCore
import Agda.Utils.Either (maybeRight)

import Scope.Core as Scope
import Scope.In   as Scope

import Paths_agda_core


main :: IO ()
main = runAgda [Backend backend]


backend :: Backend' () () () () Definition
backend = Backend'
  { backendName           = "agda-core"
  , backendVersion        = Just (showVersion version)
  , options               = ()
  , commandLineFlags      = []
  , isEnabled             = \ _       -> True
  , preCompile            = \ _       -> pure ()
  , postCompile           = \ _ _ _   -> pure ()
  , preModule             = \ _ _ _ _ -> pure $ Recompile ()
  , postModule            = \ _ _     -> checkModule
  , compileDef            = \_ _ _    -> pure
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _       -> pure True
  }


-- | Given a list of definitions,
--   construct definition and constructor membership proofs, along with constructor arity.
getModuleScope :: [Definition] -> (Defs, Cons)
getModuleScope defs =
  let ps = iterate Scope.inThere Scope.inHere
      (ds, cs) :: ([QName], [QName])
        = partitionEithers $ flip mapMaybe defs \def ->
            let name = defName def
            in case theDef def of
              Datatype{}    -> Just $ Left  name
              Function{}    -> Just $ Left  name
              Record{}      -> Just $ Left  name
              Constructor{} -> Just $ Right name
              _             -> Nothing
  in ( Map.fromList $ zip (reverse ds) ps
     , Map.fromList $ zip (reverse cs) ps
     )

checkModule :: IsMain -> TopLevelModuleName -> [Definition] -> TCM ()
checkModule IsMain tlm defs = do

  reportSDoc "agda-core.check" 5 $ text "Checking module" <+> prettyTCM tlm

  let (!gdefs, !gcons) = getModuleScope defs

  reportSDoc "agda-core.check" 5 $ text "Module definitions:"  <+> prettyTCM (Map.keys gdefs)
  reportSDoc "agda-core.check" 5 $ text "Module constructors:" <+> prettyTCM (Map.keys gcons)

  for_ defs \def -> do

    let Defn{defName, defType} = def
    let dn = prettyTCM defName

    reportSDoc "agda-core.check" 5 $ text "Checking" <+> dn

    case convert gdefs gcons (unEl defType) of
      Left e   -> reportSDoc "agda-core.check" 5 $
                        text "Couldn't convert type of" <+> dn
                    <+> text "to core syntax:" <+> text e
      Right ty -> reportSDoc "agda-core.check" 5 $ text "Type:" <+> text (show ty)

    case theDef def of
      -- NOTE(flupe): currently we only support definitions with no arguments (implying no pattern-matching)
      --              i.e functions have to be written with explicit lambdas
      Function{..}
        | not (isJust (maybeRight funProjection >>= projProper)) -- discard record projections
        , [cl]      <- funClauses
        , []        <- clausePats cl
        , Just body <- clauseBody cl
        -> case convert gdefs gcons body of
          Left e   -> reportSDoc "agda-core.check" 5 $ text "Failed to convert to core syntax:" <+> text e
          Right ct -> reportSDoc "agda-core.check" 5 $ text "Definition:" <+> text (show ct) -- liftIO $ print ct -- TODO(flupe): launch type-checker

      Datatype{}      -> reportSDoc "agda-core.check" 5 $ text "Datatypes not supported"
      Record{}        -> reportSDoc "agda-core.check" 5 $ text "Datatypes not supported"
      Axiom{}         -> reportSDoc "agda-core.check" 5 $ text "Postulates not supported"
      Primitive{}     -> reportSDoc "agda-core.check" 5 $ text "Primitives not supported"
      PrimitiveSort{} -> reportSDoc "agda-core.check" 5 $ text "Primitive sorts not supported"
      Constructor{}   -> pure () -- NOTE(flupe): will be handled when datatypes are handled

      _               -> reportSDoc "agda-core.check" 5 $ text "Unsupported, skipping" <+> prettyTCM defName

-- for now, we only check the main module
checkModule NotMain _ _ = pure ()

