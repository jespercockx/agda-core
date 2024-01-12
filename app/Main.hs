module Main where

import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable (for_)
import Data.Version (showVersion)
import Data.Map.Strict (Map)
import Data.Foldable (foldl')

import Data.Map.Strict qualified as Map

import Agda.Main
import Agda.TypeChecking.Pretty (text, prettyTCM, (<+>))
import Agda.Compiler.Backend
import Agda.Syntax.Internal
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import Agda.Core.ToCore

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



-- TODO(flupe): for datatype definitions,
--              also populate a mapping for constructors
-- TODO(flupe): for record definitions,
--              also add record fields as defs

-- | Given a list of definitions,
--  compute a mapping from def QNames to module scope membership proofs.
getModuleScope :: [Definition] -> Defs
getModuleScope (fmap defName -> defs) =
  let !n = length defs in
  Map.fromList $ zip (reverse defs)
               $ iterate Scope.inThere Scope.inHere


checkModule :: IsMain -> TopLevelModuleName -> [Definition] -> TCM ()
checkModule IsMain tlm defs = do

  reportSDoc "agda-core.check" 5 $ text "Checking module" <+> prettyTCM tlm

  let !gdefs = getModuleScope defs

  for_ defs \def -> do

    let Defn{defName, defType} = def
    let dn = prettyTCM defName

    reportSDoc "agda-core.check" 5 $ text "Checking" <+> dn

    -- TODO(flupe): convert type of def.
    case convert gdefs (unEl defType) of
      Left e   -> reportSDoc "agda-core.check" 5 $
                        text "Couldn't convert type of" <+> dn
                    <+> text "to core syntax:" <+> text e
      Right ty -> reportSDoc "agda-core.check" 5 $ text "Type:" <+> text (show ty)

    case theDef def of
      -- NOTE(flupe): currently we only support definitions with no arguments (implying no pattern-matching)
      --              i.e functions have to be written with explicit lambdas
      Function{..}
        | [cl]      <- funClauses
        , []        <- clausePats cl
        , Just body <- clauseBody cl
        -> case convert gdefs body of
          Left e   -> reportSDoc "agda-core.check" 5 $ text "Failed to convert to core syntax:" <+> text e
          Right ct -> reportSDoc "agda-core.check" 5 $ text "Definition:" <+> text (show ct) -- liftIO $ print ct -- TODO(flupe): launch type-checker

      Datatype{}      -> reportSDoc "agda-core.check" 5 $ text "Datatypes not supported"
      Record{}        -> reportSDoc "agda-core.check" 5 $ text "Datatypes not supported"
      Axiom{}         -> reportSDoc "agda-core.check" 5 $ text "Postulates not supported"
      Primitive{}     -> reportSDoc "agda-core.check" 5 $ text "Primitives not supported"
      PrimitiveSort{} -> reportSDoc "agda-core.check" 5 $ text "Primitive sorts not supported"
      Constructor{}   -> reportSDoc "agda-core.check" 5 $ text "Constructors not supported"

      _ -> reportSDoc "agda-core.check" 5 $ text "Unsupported, skipping" <+> prettyTCM defName


-- for now, we only check the main module
checkModule NotMain _ _ = pure ()
