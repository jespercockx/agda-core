module Scope.Sub where

import Scope.Core (Scope, singleton)
import Scope.Split (Split, rezzSplitLeft, splitAssoc, splitBindRight, splitComm, splitEmptyLeft, splitEmptyRight, splitJoin, splitJoinLeft, splitJoinRight, splitRefl)

type Sub = Split

subTrans :: Sub -> Sub -> Sub
subTrans p q = fst (splitAssoc p q)

subRight :: Split -> Sub
subRight p = splitComm p

subWeaken :: Sub -> Sub
subWeaken p = splitBindRight p

subEmpty :: Sub
subEmpty = splitEmptyLeft

subRefl :: Sub
subRefl = splitEmptyRight

rezzSub :: Sub -> Scope -> Scope
rezzSub p = rezzSplitLeft p

subJoin :: Scope -> Sub -> Sub -> Sub
subJoin r p q = splitJoin r p q

subJoinKeep :: Scope -> Sub -> Sub
subJoinKeep r p = splitJoinLeft r p

subJoinDrop :: Scope -> Sub -> Sub
subJoinDrop r p = splitJoinRight r p

subBindKeep :: Sub -> Sub
subBindKeep = subJoinKeep singleton

subBindDrop :: Sub -> Sub
subBindDrop = subJoinDrop singleton

joinSubLeft :: Scope -> Sub -> Sub
joinSubLeft r p = fst (splitAssoc (splitRefl r) p)

joinSubRight :: Scope -> Sub -> Sub
joinSubRight r p = fst (splitAssoc (splitComm (splitRefl r)) p)

