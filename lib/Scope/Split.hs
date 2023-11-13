module Scope.Split where

import Scope.Core (Scope, rezzBind, singleton)
import Utils.Dec (Dec)
import Utils.Erase (Erase(Erased), rezzTail)

data ListSplit = EmptyL
               | EmptyR
               | ConsL ListSplit
               | ConsR ListSplit

type Split = ListSplit

splitEmptyLeft :: Split
splitEmptyLeft = EmptyL

splitEmptyRight :: Split
splitEmptyRight = EmptyR

splitRefl :: Scope -> Split
splitRefl [] = splitEmptyLeft
splitRefl (Erased : α) = ConsL (splitRefl α)

splitComm :: Split -> Split
splitComm EmptyL = EmptyR
splitComm EmptyR = EmptyL
splitComm (ConsL p) = ConsR (splitComm p)
splitComm (ConsR p) = ConsL (splitComm p)

splitAssoc :: Split -> Split -> (Split, Split)
splitAssoc EmptyL q = (EmptyL, q)
splitAssoc EmptyR q = (q, EmptyL)
splitAssoc p EmptyR = (p, EmptyR)
splitAssoc (ConsL p) (ConsL q)
  = (ConsL (fst (splitAssoc p q)), snd (splitAssoc p q))
splitAssoc (ConsR p) (ConsL q)
  = (ConsR (fst (splitAssoc p q)), ConsL (snd (splitAssoc p q)))
splitAssoc p (ConsR q)
  = (ConsR (fst (splitAssoc p q)), ConsR (snd (splitAssoc p q)))

splitQuad :: Split -> Split -> ((Split, Split), (Split, Split))
splitQuad EmptyL q = ((EmptyL, q), (EmptyL, EmptyL))
splitQuad EmptyR q = ((q, EmptyR), (EmptyR, EmptyR))
splitQuad p EmptyL = ((EmptyL, EmptyL), (EmptyL, p))
splitQuad p EmptyR = ((EmptyR, EmptyR), (p, EmptyR))
splitQuad (ConsL p) (ConsL q)
  = ((ConsL (fst (fst (splitQuad p q))), snd (fst (splitQuad p q))),
     (ConsL (fst (snd (splitQuad p q))), snd (snd (splitQuad p q))))
splitQuad (ConsL p) (ConsR q)
  = ((ConsR (fst (fst (splitQuad p q))), snd (fst (splitQuad p q))),
     (fst (snd (splitQuad p q)), ConsL (snd (snd (splitQuad p q)))))
splitQuad (ConsR p) (ConsL q)
  = ((fst (fst (splitQuad p q)), ConsL (snd (fst (splitQuad p q)))),
     (ConsR (fst (snd (splitQuad p q))), snd (snd (splitQuad p q))))
splitQuad (ConsR p) (ConsR q)
  = ((fst (fst (splitQuad p q)), ConsR (snd (fst (splitQuad p q)))),
     (fst (snd (splitQuad p q)), ConsR (snd (snd (splitQuad p q)))))

rezzSplit :: Split -> Scope -> (Scope, Scope)
rezzSplit EmptyL r = (mempty, r)
rezzSplit EmptyR r = (r, mempty)
rezzSplit (ConsL p) r
  = (rezzBind (fst (rezzSplit p (rezzTail r))),
     snd (rezzSplit p (rezzTail r)))
rezzSplit (ConsR p) r
  = (fst (rezzSplit p (rezzTail r)),
     rezzBind (snd (rezzSplit p (rezzTail r))))

rezzSplitLeft :: Split -> Scope -> Scope
rezzSplitLeft p r = fst (rezzSplit p r)

rezzSplitRight :: Split -> Scope -> Scope
rezzSplitRight p r = snd (rezzSplit p r)

splitJoinLeft :: Scope -> Split -> Split
splitJoinLeft [] p = p
splitJoinLeft (Erased : α) p = ConsL (splitJoinLeft α p)

splitJoinRight :: Scope -> Split -> Split
splitJoinRight [] p = p
splitJoinRight (Erased : α) p = ConsR (splitJoinRight α p)

splitJoin :: Scope -> Split -> Split -> Split
splitJoin r EmptyL q = splitJoinRight r q
splitJoin r EmptyR q = splitJoinLeft r q
splitJoin r (ConsL p) q = ConsL (splitJoin (rezzTail r) p q)
splitJoin r (ConsR p) q = ConsR (splitJoin (rezzTail r) p q)

splitBindLeft :: Split -> Split
splitBindLeft = splitJoinLeft singleton

splitBindRight :: Split -> Split
splitBindRight = splitJoinRight singleton

decSplit :: Split -> Split -> Dec
decSplit EmptyL EmptyL = True
decSplit EmptyR EmptyR = True
decSplit (ConsL p) (ConsL q) = decSplit p q
decSplit (ConsR p) (ConsR q) = decSplit p q
decSplit EmptyL EmptyR = False
decSplit EmptyL (ConsR q) = False
decSplit EmptyR EmptyL = False
decSplit EmptyR (ConsL q) = False
decSplit (ConsL p) EmptyR = False
decSplit (ConsL p) (ConsR q) = False
decSplit (ConsR p) EmptyL = False
decSplit (ConsR p) (ConsL q) = False

