
module Agda.Core.PrettyPrint (NameMap(..), prettyCore) where


import Scope.In (Index(..))
import Agda.Core.Syntax qualified as Core
import GHC.Natural (Natural)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map (lookup)
import Agda.Utils.Maybe (fromMaybe)
import Agda.Core.UtilsH (indexToNat)
import Agda.Utils.List2 (toList1)
import qualified Agda.Core.Signature as Core

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


{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.Term where
-- could use some views to fuse the cases of TVar TSort and TDef
-- should use a Reader Monad for the Map
-- should return a Doc instead of a String
  prettyCore :: NameMap -> Core.Term -> String
  prettyCore ma = prettyCoreTermAux ma Something

prettyCoreTermAux :: NameMap -> AboveCoreTerm -> Core.Term -> String
prettyCoreTermAux m IsRigthApp term = -- to avoid parenthesis
  case term of
    Core.TVar _ -> prettyCoreTermAux m Something term
    Core.TSort _ -> prettyCoreTermAux m Something term
    Core.TDef _ -> prettyCoreTermAux m Something term
    _ -> "(" <> prettyCoreTermAux m Something term <> ")"
prettyCoreTermAux m IsLeftApp term = -- to avoid parenthesis
  case term of
    Core.TVar _ -> prettyCoreTermAux m Something term
    Core.TSort _ -> prettyCoreTermAux m Something term
    Core.TDef _ -> prettyCoreTermAux m Something term
    Core.TApp u v -> prettyCoreTermAux m IsLeftApp u <> " • " <> prettyCoreTermAux m IsRigthApp v
    _ -> "(" <> prettyCoreTermAux m Something term <> ")"
prettyCoreTermAux m Something term =
  case term of
    Core.TVar n -> show $ indexToNat n
    Core.TSort (Core.STyp n) -> "S" <> show n
    Core.TDef n -> let k = indexToNat n in fromMaybe ("F" <> show k) (Map.lookup k (nameDefs m))
    Core.TPi (Core.El _ a) (Core.El _ b) -> "∀(" <> prettyCoreTermAux m Something a <> ")" <> prettyCoreTermAux m IsForall b
    Core.TLam t -> prettyCoreTermAux m (IsLambda 1) t
    Core.TApp u v -> prettyCoreTermAux m IsLeftApp u <> " • " <> prettyCoreTermAux m IsRigthApp v
    Core.TCon d c trms -> let k = (indexToNat d, indexToNat c) in fromMaybe ("C" <> show k) (Map.lookup k (nameCons m)) <> "[ " <> prettyCore m trms <>"]"
    Core.TData d pars ixs -> let k = indexToNat d in fromMaybe ("D" <> show k) (Map.lookup k (nameDefs m)) <> prettyCore m pars <> prettyCore m ixs
    t -> show t
prettyCoreTermAux m IsForall term = -- when we have several ∀
    case term of
      Core.TPi (Core.El _ a) (Core.El _ b) -> "(" <> prettyCoreTermAux m Something a <> ")" <> prettyCoreTermAux m IsForall b
      t -> "." <> prettyCoreTermAux m Something t
prettyCoreTermAux m (IsLambda n) term = -- when we have several λ
    case term of
      Core.TLam t -> prettyCoreTermAux m (IsLambda (n + 1)) t
      _ -> ("λ" <> show n <> ". ") <> prettyCoreTermAux m Something term

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.Type where
  prettyCore :: NameMap -> Core.Type -> String
  prettyCore m ty =
    case ty of
      Core.El (Core.STyp n) t -> "El{S" <> show n <> "} " <> prettyCore m t

{- ───────────────────────────────────────────────────────────────────────────────────────────── -}
instance PrettyCore Core.TermS where
  prettyCore :: NameMap -> Core.TermS -> String
  prettyCore m trms =
    case trms of
      Core.TSNil -> ""
      Core.TSCons t ts -> prettyCoreTermAux m IsRigthApp t <> " " <> prettyCore m ts

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

