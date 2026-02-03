module Agda.Core where

-- this should stay in sync with the modules defined in agda-core.cabal
open import Agda.Core.Checkers.Converter public
open import Agda.Core.Checkers.TypeCheck public
open import Agda.Core.GlobalScope public
open import Agda.Core.Prelude public
open import Agda.Core.Reduce public
open import Agda.Core.Rules.Conversion public
open import Agda.Core.Rules.Typing public
open import Agda.Core.Syntax.Context public
open import Agda.Core.Syntax.Term public
open import Agda.Core.Syntax.Signature public
open import Agda.Core.Syntax.Strengthening public
open import Agda.Core.Syntax.Substitute public
open import Agda.Core.Syntax.Weakening public
open import Agda.Core.TCM.Instances public
open import Agda.Core.TCM.TCM public
