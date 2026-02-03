
module Agda.Core.UtilsH where

import Scope.In (Index(..))
import Agda.TypeChecking.Pretty (text, prettyTCM, (<+>), Doc)

import Control.Monad.IO.Class (liftIO, MonadIO)
import Agda.Compiler.Backend (TCM, reportSDoc, MonadDebug)
import Agda.TypeChecking.Monad (VerboseLevel, VerboseKey)

import System.Console.ANSI
    ( SGR(SetColor, SetConsoleIntensity),
      ConsoleIntensity(BoldIntensity),
      ConsoleLayer(Foreground),
      ColorIntensity(Vivid),
      Color(..),
      getTerminalSize,
      setSGR )
import GHC.Natural (Natural, naturalToInteger)
import GHC.Num (integerToInt)

import Debug.Trace


indexToNat :: Index -> Natural
indexToNat  Zero = 0
indexToNat (Suc n) = indexToNat n + 1

indexToInt :: Index -> Int
indexToInt = integerToInt . naturalToInteger . indexToNat

listToUnitList :: [ a ] -> [()]
listToUnitList [] = []
listToUnitList (_ : q) = () : listToUnitList q


-- line of ─
lineInDoc :: TCM Doc
lineInDoc =
    let width = getTerminalSize >>= maybe (return 0) (return . snd) in
    liftIO width >>= text . (`replicate` '─')

-- message in a box
boxInDoc :: String -> TCM Doc
boxInDoc message = do
    let width = getTerminalSize >>= maybe (return 0) (return . snd)
    let lm = length message
    let spaceToCenter = width >>= \varx -> text $ replicate (div (varx - lm - 4) 2) ' '
    let line1 = spaceToCenter <> text ("┌─" <> replicate lm '─' <> "─┐" <> "\n")
        line2 = spaceToCenter <> text ("│ " <>     message      <> " │" <> "\n")
        line3 = spaceToCenter <> text ("└─" <> replicate lm '─' <> "─┘"        )

    liftIO $ line1 <> line2 <> line3


reportSDocFailure ::  (MonadDebug m, MonadIO m) => VerboseKey -> TCM Doc -> m ()
reportSDocFailure s m = do
    liftIO $ setSGR [ SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red ]
    reportSDoc s 1 m
    liftIO $ setSGR []

reportSDocWarning :: (MonadDebug m, MonadIO m) =>  VerboseKey -> VerboseLevel -> TCM Doc -> m ()
reportSDocWarning s k m = do
    liftIO $ setSGR [ SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Yellow ]
    reportSDoc s k m
    liftIO $ setSGR []


-- Helper to add color to Debug.trace output
traceColor :: String -> String -> a -> a
traceColor color msg = trace (color ++ msg ++ "\x1b[0m")

traceRed, traceGreen, traceYellow, traceBlue, traceMagenta, traceCyan :: String -> a -> a
traceRed     = traceColor "\x1b[31m"
traceGreen   = traceColor "\x1b[32m"
traceYellow  = traceColor "\x1b[33m"
traceBlue    = traceColor "\x1b[34m"
traceMagenta = traceColor "\x1b[35m"
traceCyan    = traceColor "\x1b[36m"
