module Scope where

import Utils.Erase (Erase(Erased), rezzCong2, rezzErase, rezzTail)

type Scope name = [Erase]

empty :: Scope name
empty = []

singleton :: Scope name
singleton = [Erased]

bind :: Scope name -> Scope name
bind α = singleton <> α

data Join = EmptyL
          | EmptyR
          | ConsL Join
          | ConsR Join

type Split = Join

splitEmptyLeft :: Split
splitEmptyLeft = EmptyL

splitEmptyRight :: Split
splitEmptyRight = EmptyR

splitRefl :: Scope name -> Split
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

rezzBind :: Scope name -> Scope name
rezzBind = rezzCong2 (:) rezzErase

rezzSplit :: Split -> Scope name -> (Scope name, Scope name)
rezzSplit EmptyL r = (empty, r)
rezzSplit EmptyR r = (r, empty)
rezzSplit (ConsL p) r
  = (rezzBind (fst (rezzSplit p (rezzTail r))),
     snd (rezzSplit p (rezzTail r)))
rezzSplit (ConsR p) r
  = (fst (rezzSplit p (rezzTail r)),
     rezzBind (snd (rezzSplit p (rezzTail r))))

rezzSplitLeft :: Split -> Scope name -> Scope name
rezzSplitLeft p r = fst (rezzSplit p r)

rezzSplitRight :: Split -> Scope name -> Scope name
rezzSplitRight p r = snd (rezzSplit p r)

splitJoinLeft :: Scope name -> Split -> Split
splitJoinLeft [] p = p
splitJoinLeft (Erased : α) p = ConsL (splitJoinLeft α p)

splitJoinRight :: Scope name -> Split -> Split
splitJoinRight [] p = p
splitJoinRight (Erased : α) p = ConsR (splitJoinRight α p)

splitJoin :: Scope name -> Split -> Split -> Split
splitJoin r EmptyL q = splitJoinRight r q
splitJoin r EmptyR q = splitJoinLeft r q
splitJoin r (ConsL p) q = ConsL (splitJoin (rezzTail r) p q)
splitJoin r (ConsR p) q = ConsR (splitJoin (rezzTail r) p q)

splitBindLeft :: Split -> Split
splitBindLeft = splitJoinLeft singleton

splitBindRight :: Split -> Split
splitBindRight = splitJoinRight singleton

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

rezzSub :: Sub -> Scope name -> Scope name
rezzSub p = rezzSplitLeft p

subJoin :: Scope name -> Sub -> Sub -> Sub
subJoin r p q = splitJoin r p q

subJoinKeep :: Scope name -> Sub -> Sub
subJoinKeep r p = splitJoinLeft r p

subJoinDrop :: Scope name -> Sub -> Sub
subJoinDrop r p = splitJoinRight r p

subBindKeep :: Sub -> Sub
subBindKeep = subJoinKeep singleton

subBindDrop :: Sub -> Sub
subBindDrop = subJoinDrop singleton

joinSubLeft :: Scope name -> Sub -> Sub
joinSubLeft r p = fst (splitAssoc (splitRefl r) p)

joinSubRight :: Scope name -> Sub -> Sub
joinSubRight r p = fst (splitAssoc (splitComm (splitRefl r)) p)

type In = Sub

coerce :: Sub -> In -> In
coerce p q = subTrans q p

here :: In
here = splitRefl singleton

there :: In -> In
there = subBindDrop

bindSubToIn :: Sub -> In
bindSubToIn = joinSubLeft singleton

singCase :: In -> a -> a
singCase EmptyR f = f
singCase (ConsL _) f = f

splitCase :: Split -> In -> (In -> a) -> (In -> a) -> a
splitCase EmptyL EmptyR f g = g here
splitCase EmptyL (ConsL q) f g = g here
splitCase EmptyL (ConsR q) f g = g (there q)
splitCase EmptyR EmptyR f g = f here
splitCase EmptyR (ConsL q) f g = f here
splitCase EmptyR (ConsR q) f g = f (there q)
splitCase (ConsL p) EmptyR f g = f here
splitCase (ConsL p) (ConsL q) f g = f here
splitCase (ConsL p) (ConsR q) f g = splitCase p q (f . there) g
splitCase (ConsR p) EmptyR f g = g here
splitCase (ConsR p) (ConsL q) f g = g here
splitCase (ConsR p) (ConsR q) f g = splitCase p q f (g . there)

joinCase :: Scope name -> In -> (In -> a) -> (In -> a) -> a
joinCase r = splitCase (splitRefl r)

bindCase :: In -> a -> (In -> a) -> a
bindCase p f g = joinCase singleton p (\ q -> singCase q f) g

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
