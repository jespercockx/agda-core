module Scope.All where

import Scope.In (In)
import Scope.Split (ListSplit(ConsL, ConsR, EmptyR))
import qualified Utils.List (All(ACons, ANil))

type All p = Utils.List.All p

allEmpty :: All p
allEmpty = Utils.List.ANil

allSingl :: p -> All p
allSingl p = Utils.List.ACons p Utils.List.ANil

getAllSingl :: All p -> p
getAllSingl (Utils.List.ACons p Utils.List.ANil) = p

allJoin :: All p -> All p -> All p
allJoin Utils.List.ANil pbs = pbs
allJoin (Utils.List.ACons px pas) pbs
  = Utils.List.ACons px (allJoin pas pbs)

lookupAll :: All p -> In -> p
lookupAll ps EmptyR = getAllSingl ps
lookupAll (Utils.List.ACons px _) (ConsL _) = px
lookupAll (Utils.List.ACons _ ps) (ConsR q) = lookupAll ps q

