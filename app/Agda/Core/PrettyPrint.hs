
module Agda.Core.PrettyPrint (NameMap(..), prettyCore) where


import Scope.In (Index(..))
import Agda.Core.Syntax.Term        qualified as Core
import Agda.Core.Syntax.Context     qualified as Core
import  Agda.Core.Syntax.Signature  qualified as Core
import GHC.Natural (Natural)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map (lookup)
import Agda.Utils.Maybe (fromMaybe)
import Agda.Core.UtilsH (indexToNat)
import Agda.Utils.List2 (toList1)
import Agda.Utils.Impossible (__IMPOSSIBLE__)

data AboveCoreTerm =
    Something
  | IsForall
  | IsLeftApp
  | IsRigthApp
  | IsLambda Natural

data NameMap = NameMap {
  nameDefs      :: Map Natural String,
  nameData      :: Map Natural String,
  nameCons      :: Map (Natural, Natural) String
}
class PrettyCore a where
  prettyCore :: NameMap -> a -> String



printDef :: NameMap -> Index -> String
printDef m n = let k = indexToNat n in fromMaybe ("F" <> show k) (Map.lookup k (nameDefs m))
printNameData :: NameMap -> Index -> String
printNameData m d = let k = indexToNat d in fromMaybe ("D" <> show k) (Map.lookup k (nameDefs m))
printNameCon :: NameMap -> Index -> Index -> String
printNameCon m d c = let k = (indexToNat d, indexToNat c) in fromMaybe ("C" <> show k) (Map.lookup k (nameCons m))

requiresParentheses :: AboveCoreTerm -> Core.Term -> Bool
requiresParentheses Something    _ = False
requiresParentheses IsForall     _ = False
requiresParentheses (IsLambda n) _ = False
requiresParentheses _ (Core.TVar _)   = False
requiresParentheses _ (Core.TDef _)   = False
requiresParentheses _ (Core.TSort _)  = False
requiresParentheses _ (Core.TAnn {})  = False
requiresParentheses _ (Core.TCase {}) = False
requiresParentheses IsLeftApp    _ = True
requiresParentheses IsRigthApp   _ = True

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.Term where
-- should use a Reader Monad for the Map
-- should return a Doc instead of a String
  prettyCore :: NameMap -> Core.Term -> String
  prettyCore ma = prettyCoreTermAux ma Something

prettyCoreTermAux :: NameMap -> AboveCoreTerm -> Core.Term -> String
prettyCoreTermAux m IsRigthApp term = -- to avoid parenthesis
  if requiresParentheses IsRigthApp term then
    "(" <> prettyCoreTermAux m Something term <> ")"
  else
    prettyCoreTermAux m Something term
prettyCoreTermAux m IsLeftApp (Core.TApp u v) =
  prettyCoreTermAux m IsLeftApp u <> " • " <> prettyCoreTermAux m IsRigthApp v
prettyCoreTermAux m IsLeftApp term = -- to avoid parenthesis
    if requiresParentheses IsLeftApp term then
    "(" <> prettyCoreTermAux m Something term <> ")"
  else
    prettyCoreTermAux m Something term
prettyCoreTermAux m Something term =
  case term of
    Core.TVar n -> show $ indexToNat n
    Core.TSort s -> prettyCore m s
    Core.TDef n -> printDef m n
    Core.TPi (Core.El _ a) (Core.El _ b) -> "∀(" <> prettyCoreTermAux m Something a <> ")" <> prettyCoreTermAux m IsForall b
    Core.TLam t -> prettyCoreTermAux m (IsLambda 1) t
    Core.TApp u v -> prettyCoreTermAux m IsLeftApp u <> " • " <> prettyCoreTermAux m IsRigthApp v
    Core.TCon d c trms -> printNameCon m d c <> "[ " <> prettyCore m trms <>"]"
    Core.TData d pars ixs -> printNameData m d <> prettyCore m pars <> prettyCore m ixs
    Core.TProj _ _ -> "projection not implemented"
    Core.TCase d r u bs ty -> "Case" <> printNameData m d <> prettyCore m u <> "of" <> prettyCoreBranches m d bs <> ":" <> prettyCore m ty
    Core.TLet _ _  -> "let binding not implemented"
    Core.TAnn u ty -> "(" <>prettyCore m u <> " : " <> prettyCore m ty <> ")"
prettyCoreTermAux m IsForall term = -- when we have several ∀
    case term of
      Core.TPi (Core.El _ a) (Core.El _ b) -> "(" <> prettyCoreTermAux m Something a <> ")" <> prettyCoreTermAux m IsForall b
      t -> "." <> prettyCoreTermAux m Something t
prettyCoreTermAux m (IsLambda n) term = -- when we have several λ
    case term of
      Core.TLam t -> prettyCoreTermAux m (IsLambda (n + 1)) t
      _ -> ("λ" <> show n <> ". ") <> prettyCoreTermAux m Something term

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.TermS where
  prettyCore :: NameMap -> Core.TermS -> String
  prettyCore m Core.TSNil = ""
  prettyCore m (Core.TSCons t ts) = prettyCoreTermAux m IsRigthApp t <> " " <> prettyCore m t

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.Sort where
  prettyCore :: NameMap -> Core.Sort -> String
  prettyCore m (Core.STyp n) = "S" <> show n

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.Type where
  prettyCore :: NameMap -> Core.Type -> String
  prettyCore m ty =
    case ty of
      Core.El (Core.STyp n) t -> "El{S" <> show n <> "} " <> prettyCore m t

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
prettyCoreBranches :: NameMap -> Index -> Core.Branches -> String
prettyCoreBranches m d Core.BsNil = "{}"
prettyCoreBranches m d (Core.BsCons b ts) =
  "{ " <> prettyCoreBranch m d b <> " | " <> prettyCoreBranchesAux m ts <> " }"
  where prettyCoreBranchesAux :: NameMap -> Core.Branches -> String
        prettyCoreBranchesAux m0 Core.BsNil = ""
        prettyCoreBranchesAux m0 (Core.BsCons b0 ts0) =
           " | " <> prettyCoreBranch m0 d b0 <> prettyCoreBranchesAux m0 ts0

prettyCoreBranch :: NameMap -> Index -> Core.Branch -> String
prettyCoreBranch m d (Core.BBranch c _ u) = printNameCon m d c <> " => " <> prettyCore m u

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.Telescope where
  prettyCore :: NameMap -> Core.Telescope -> String
  prettyCore m0 t0 =
    case t0 of
      Core.EmptyTel -> "[]"
      Core.ExtendTel (Core.El _ trm0) t1 -> "[ " <> prettyCore m0 trm0 <> prettyCoreTelescopeAux m0 t1 <> " ]"
    where prettyCoreTelescopeAux :: NameMap -> Core.Telescope -> String
          prettyCoreTelescopeAux m trms =
            case trms of
              Core.EmptyTel -> ""
              Core.ExtendTel (Core.El _ trm) t -> ", " <> prettyCore m trm <> prettyCoreTelescopeAux m t

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.Datatype where
  prettyCore :: NameMap -> Core.Datatype -> String
  prettyCore m d = "Is a datatype"

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.Constructor where
  prettyCore :: NameMap -> Core.Constructor -> String
  prettyCore m d = "Is a constructor"

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.Defn where
  prettyCore :: NameMap -> Core.Defn -> String
  prettyCore m (Core.FunctionDefn    t) =
    prettyCore m t
  prettyCore m (Core.DatatypeDefn    d) =
    prettyCore m d
  prettyCore m (Core.ConstructorDefn c) =
    prettyCore m c

instance PrettyCore Core.Definition where
  prettyCore :: NameMap -> Core.Definition -> String
  prettyCore m Core.Definition { defName, defType, theDef } = 
    "Core.Definition{" <> defName <> "<is a defType>" <> prettyCore m theDef <> "}" 

