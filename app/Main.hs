module Main where

import Data.Version (showVersion)

import Agda.Main
import Agda.TypeChecking.Pretty (text)
import Agda.Compiler.Backend

import Paths_agda_core

backend :: Backend' () () () () ()
backend = Backend'
  { backendName           = "agda-core"
  , backendVersion        = Just (showVersion version)
  , options               = ()
  , commandLineFlags      = []
  , isEnabled             = \ _         ->  True
  , preCompile            = \ _         -> pure ()
  , postCompile           = \ _ _ _     -> pure ()
  , preModule             = \ _ _ _ _   -> pure $ Recompile ()
  , postModule            = \ _ _ _ _ _ -> pure ()
  , compileDef            = \_ _ _ -> compile
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> pure True
  }

compile :: Definition -> TCM ()
compile def =
  withCurrentModule (qnameModule $ defName def) $ 
    setCurrentRange (nameBindingSite $ qnameName $ defName def) $
      case theDef def of
        _          -> genericDocError =<< text "Kind of definition not supported."

main :: IO ()
main = runAgda [Backend backend]
