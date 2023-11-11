module Scope.In where

import Scope.Core (Scope, singleton)
import Scope.Split (ListSplit(ConsL, ConsR, EmptyL, EmptyR), Split, splitRefl)
import Scope.Sub (Sub, joinSubLeft, subBindDrop, subTrans)

type In = Sub

coerce :: Sub -> In -> In
coerce p q = subTrans q p

inHere :: In
inHere = splitRefl singleton

inThere :: In -> In
inThere = subBindDrop

bindSubToIn :: Sub -> In
bindSubToIn = joinSubLeft singleton

inEmptyCase :: a
inEmptyCase = error "impossible"

inSingCase :: In -> a -> a
inSingCase EmptyR f = f
inSingCase (ConsL _) f = f

inSplitCase :: Split -> In -> (In -> a) -> (In -> a) -> a
inSplitCase EmptyL EmptyR f g = g inHere
inSplitCase EmptyL (ConsL q) f g = g inHere
inSplitCase EmptyL (ConsR q) f g = g (inThere q)
inSplitCase EmptyR EmptyR f g = f inHere
inSplitCase EmptyR (ConsL q) f g = f inHere
inSplitCase EmptyR (ConsR q) f g = f (inThere q)
inSplitCase (ConsL p) EmptyR f g = f inHere
inSplitCase (ConsL p) (ConsL q) f g = f inHere
inSplitCase (ConsL p) (ConsR q) f g
  = inSplitCase p q (f . inThere) g
inSplitCase (ConsR p) EmptyR f g = g inHere
inSplitCase (ConsR p) (ConsL q) f g = g inHere
inSplitCase (ConsR p) (ConsR q) f g
  = inSplitCase p q f (g . inThere)

inJoinCase :: Scope -> In -> (In -> a) -> (In -> a) -> a
inJoinCase r = inSplitCase (splitRefl r)

inBindCase :: In -> a -> (In -> a) -> a
inBindCase p f g = inJoinCase singleton p (\ q -> inSingCase q f) g

