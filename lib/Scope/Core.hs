module Scope.Core where

import Utils.Erase (Erase(Erased), rezzCong2, rezzErase)

type Scope = [Erase]

singleton :: Scope
singleton = [Erased]

bind :: Scope -> Scope
bind α = singleton <> α

rezzBind :: Scope -> Scope
rezzBind = rezzCong2 (:) rezzErase

