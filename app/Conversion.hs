-- | Conversion from Agda's internal syntax to core representation
module Conversion
  ( convertExpr
  ) where

import Agda.Syntax.Abstract qualified as A
-- import Agda.TypeChecking.Monad.Base
-- import Agda.TypeChecking.Pretty (text)
import Syntax
import Scope.In

fetchName :: A.Name -> Maybe In
fetchName = undefined

fetchQName :: A.QName -> Maybe In
fetchQName = undefined

convertExpr :: A.Expr -> Maybe Term
convertExpr (A.Var name)              = TVar <$> fetchName name
convertExpr (A.Def' qname A.NoSuffix) = TDef <$> fetchQName qname
convertExpr (A.Con aname) =
  -- TODO(flupe): ensure that constructor expects no arguments here
  Nothing
convertExpr (A.App ai u v) = Nothing
convertExpr _ = Nothing
